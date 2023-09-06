/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * cocoa utilities
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/cocoa.h"

// external includes
#include <CoCoA/BigInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyRing.H>

// std includes
#include <sstream>

// internal includes
#include "expr/node_traversal.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

#define LETTER(c) (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z'))

template <typename O>
std::string extractStr(const O& sym)
{
  std::ostringstream o;
  o << sym;
  return o.str();
}

// CoCoA symbols must start with a letter and contain only letters, numbers, and
// underscores.
//
// Our encoding is described within
CoCoA::symbol cocoaSym(const std::string& varName, std::optional<size_t> index)
{
  std::ostringstream o;
  // o << "v_";
  for (const auto c : varName)
  {
    uint8_t code = c;
    if (LETTER(c) || ('0' <= c && c <= '9'))
    {
      // letters and numbers as themselves
      o << c;
    }
    else if ('_' == c)
    {
      // _ as __
      o << "__";
    }
    else
    {
      // other as _xXX
      o << "_x"
        << "0123456789abcdef"[code & 0x0f]
        << "0123456789abcdef"[(code >> 4) & 0x0f];
    }
  }
  // if we're starting with something bad, prepend p__; note that the above
  // never produces __.
  std::string s = o.str();
  if (!LETTER(s[0]))
  {
    Unimplemented();
    s.insert(0, "p__");
  }
  return index.has_value() ? CoCoA::symbol(s, *index) : CoCoA::symbol(s);
}

CocoaEncoder::CocoaEncoder(const FfSize& size)
    : FieldObj(size),
      d_coeffField(
          CoCoA::NewZZmod(CoCoA::BigIntFromString(size.d_val.toString())))
{
}

CoCoA::symbol CocoaEncoder::freshSym(const std::string& varName,
                                     std::optional<size_t> index)
{
  Trace("ff::cocoa::sym") << "CoCoA sym for " << varName;
  if (index.has_value())
  {
    Trace("ff::cocoa::sym") << "[" << *index << "]";
  }
  Trace("ff::cocoa::sym") << std::endl;
  Assert(d_stage == Stage::Scan);
  std::optional<size_t> suffix = {};
  CoCoA::symbol sym("dummy");
  std::string symString;
  do
  {
    std::string n = suffix.has_value()
                        ? varName + "_" + std::to_string(suffix.value())
                        : varName;
    sym = cocoaSym(n, index);
    symString = extractStr(sym);
    if (suffix.has_value())
    {
      *suffix += 1;
    }
    else
    {
      suffix = std::make_optional(0);
    }
  } while (d_vars.count(symString));
  d_vars.insert(symString);
  d_syms.push_back(sym);
  return sym;
}

void CocoaEncoder::endScan()
{
  Assert(d_stage == Stage::Scan);
  d_stage = Stage::Encode;
  d_polyRing = CoCoA::NewPolyRing(d_coeffField, d_syms);
  for (size_t i = 0; i < d_syms.size(); ++i)
  {
    d_symPolys.insert({extractStr(d_syms[i]), CoCoA::indet(*d_polyRing, i)});
  }
}

void CocoaEncoder::addFact(const Node& fact)
{
  if (d_stage == Stage::Scan)
  {
    Assert(isFfFact(fact));
    for (const auto& node :
         NodeDfsIterable(fact, VisitOrder::POSTORDER, [this](TNode nn) {
           return d_scanned.count(nn) || !(isFfTerm(nn) || isFfFact(nn));
         }))
    {
      if (!d_scanned.insert(node).second)
      {
        continue;
      }
      if (node.isVar())
      {
        // TODO: leaves
        CoCoA::symbol sym = freshSym(node.getName());
        Assert(!d_varSyms.count(node));
        Assert(!d_symNodes.count(extractStr(sym)));
        d_varSyms.insert({node, sym});
        d_symNodes.insert({extractStr(sym), node});
      }
      else if (node.getKind() == kind::NOT && isFfFact(node))
      {
        CoCoA::symbol sym = freshSym("diseq", d_diseqSyms.size());
        d_diseqSyms.insert({node, sym});
      }
      else if (node.getKind() == kind::FINITE_FIELD_BITSUM)
      {
        CoCoA::symbol sym = freshSym("bitsum", d_bitsumSyms.size());
        d_bitsumSyms.insert({node, sym});
        d_symNodes.insert({extractStr(sym), node});
      }
    }
  }
  else
  {
    Assert(d_stage == Stage::Encode);
    encodeFact(fact);
    d_polys.push_back(d_cache.at(fact));
  }
}

std::optional<std::pair<Node, Node>> CocoaEncoder::parseEquality(
    const CoCoA::RingElem& poly) const
{
  if (CoCoA::deg(poly) != 1) return {};
  if (CoCoA::NumTerms(poly) != 2) return {};
  if (!CoCoA::IsZero(CoCoA::ConstantCoeff(poly))) return {};
  auto it0 = CoCoA::BeginIter(poly);
  auto it1 = it0;
  ++it1;
  if (!CoCoA::IsOne(-(CoCoA::coeff(it0) * CoCoA::coeff(it1)))) return {};
  ssize_t i0, i1;
  AlwaysAssert(CoCoA::IsIndet(i0, CoCoA::PP(it0)));
  AlwaysAssert(CoCoA::IsIndet(i1, CoCoA::PP(it1)));
  std::string var0 = extractStr(CoCoA::indet(*d_polyRing, i0));
  if (!d_symNodes.count(var0)) return {};
  std::string var1 = extractStr(CoCoA::indet(*d_polyRing, i1));
  if (!d_symNodes.count(var1)) return {};
  return {{d_symNodes.at(var0), d_symNodes.at(var1)}};
}

std::vector<Node> CocoaEncoder::bitsums() const
{
  std::vector<Node> bs;
  for (const auto& [b, _] : d_bitsumSyms)
  {
    bs.push_back(b);
  }
  return bs;
}

const Node& CocoaEncoder::symNode(CoCoA::symbol s) const
{
  Assert(d_symNodes.count(extractStr(s)));
  return d_symNodes.at(extractStr(s));
}

bool CocoaEncoder::hasNode(CoCoA::symbol s) const
{
  return d_symNodes.count(extractStr(s));
}

std::vector<std::pair<size_t, Node>> CocoaEncoder::nodeIndets() const
{
  std::vector<std::pair<size_t, Node>> out;
  for (size_t i = 0; i < d_syms.size(); ++i)
  {
    if (hasNode(d_syms[i]))
    {
      Node n = symNode(d_syms[i]);
      if (isFfLeaf(n))
      {
        out.emplace_back(i, n);
      }
    }
  }
  return out;
}

FiniteFieldValue CocoaEncoder::cocoaFfToFfVal(const CoCoA::RingElem& elem)
{
  Assert(CoCoA::owner(elem) == d_coeffField);
  std::ostringstream valStr;
  valStr << elem;
  Integer integer(valStr.str(), 10);
  return {integer, size()};
}

const CoCoA::RingElem& CocoaEncoder::symPoly(CoCoA::symbol s) const
{
  Assert(d_symPolys.count(extractStr(s)));
  return d_symPolys.at(extractStr(s));
}

void CocoaEncoder::encodeTerm(const Node& t)
{
  Assert(d_stage == Stage::Encode);

  for (const auto& node :
       NodeDfsIterable(t, VisitOrder::POSTORDER, [this](TNode nn) {
         return d_cache.count(nn) || !(isFfTerm(nn) || isFfFact(nn));
       }))
  {
    CoCoA::RingElem elem;
    if (node.isVar())
    {
      elem = symPoly(d_varSyms.at(node));
    }
    else
    {
      switch (node.getKind())
      {
        case kind::FINITE_FIELD_ADD:
        {
          elem = CoCoA::zero(*d_polyRing);
          for (const auto& c : node)
          {
            elem += d_cache[c];
          }
          break;
        }
        case kind::FINITE_FIELD_MULT:
        {
          elem = CoCoA::one(*d_polyRing);
          for (const auto& c : node)
          {
            elem *= d_cache[c];
          }
          break;
        }
        case kind::FINITE_FIELD_BITSUM:
        {
          CoCoA::RingElem sum = CoCoA::zero(*d_polyRing);
          CoCoA::RingElem two = CoCoA::one(*d_polyRing) * 2;
          CoCoA::RingElem twoPow = CoCoA::one(*d_polyRing);
          for (const auto& c : node)
          {
            sum += twoPow * d_cache[c];
            twoPow *= two;
          }
          elem = symPoly(d_bitsumSyms.at(node));
          sum -= elem;
          d_bitsumPolys.push_back(sum);
          break;
        }
        case kind::CONST_FINITE_FIELD:
        {
          elem = CoCoA::one(*d_polyRing)
                 * CoCoA::BigIntFromString(
                     node.getConst<FiniteFieldValue>().getValue().toString());
          break;
        }
        default: Unimplemented() << node;
      }
    }
    d_cache.insert({node, elem});
  }
}

void CocoaEncoder::encodeFact(const Node& f)
{
  Assert(d_stage == Stage::Encode);
  Assert(isFfFact(f));
  if (f.getKind() == kind::EQUAL)
  {
    // ==
    encodeTerm(f[0]);
    encodeTerm(f[1]);
    d_cache.insert({f, d_cache.at(f[0]) - d_cache.at(f[1])});
  }
  else
  {
    // !=
    encodeTerm(f[0][0]);
    encodeTerm(f[0][1]);
    CoCoA::RingElem diff = d_cache.at(f[0][0]) - d_cache.at(f[0][1]);
    d_cache.insert({f, diff * symPoly(d_diseqSyms.at(f)) - 1});
  }
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
