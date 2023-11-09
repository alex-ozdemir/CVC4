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
 * a split groebner basis
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/split_gb.h"

// external includes
#include <CoCoA/BigIntOps.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-MinPoly.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/SparsePolyRing.H>

// std includes
#include <variant>

// internal includes
#include "base/output.h"
#include "theory/ff/multi_roots.h"
#include "theory/ff/parse.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

namespace {

std::unique_ptr<AssignmentEnumerator> applyRule(const Gb& gb,
                                                const CoCoA::ring& polyRing,
                                                const PartialRoot& r)
{
  Assert(static_cast<long>(r.size()) == CoCoA::NumIndets(polyRing));
  Assert(std::any_of(
      r.begin(), r.end(), [](const auto& v) { return !v.has_value(); }));
  // (1) are the any polynomials that are univariate in an unassigned variable?
  const auto& gens = gb.basis();
  for (const auto& p : gens)
  {
    int varNumber = CoCoA::UnivariateIndetIndex(p);
    if (varNumber >= 0 && !r[varNumber].has_value())
    {
      return factorEnumerator(p);
    }
  }
  // (2) if dimension 0, then compute such a polynomial
  if (gb.zeroDimensional())
  {
    // If zero-dimensional, we compute a minimal polynomial in some unset
    // variable.
    for (size_t i = 0; i < r.size(); ++i)
    {
      if (!r[i].has_value())
      {
        CoCoA::RingElem minPoly =
            gb.minimalPolynomial(CoCoA::indet(polyRing, i));
        return factorEnumerator(minPoly);
      }
    }
    Unreachable() << "There should be some unset var";
  }
  else
  {
    // If positive dimension, we make a list of unset variables and
    // round-robin guess.
    //
    // TODO(aozdemir): better model construction (cvc5-wishues/issues/138)
    std::vector<CoCoA::RingElem> toGuess{};
    for (size_t i = 0; i < r.size(); ++i)
    {
      if (!r[i].has_value())
      {
        toGuess.push_back(CoCoA::indet(polyRing, i));
      }
    }
    return std::make_unique<RoundRobinEnumerator>(toGuess,
                                                  polyRing->myBaseRing());
  }
  Unreachable();
  return nullptr;
}

}  // namespace


SplitGb2 splitGb(const std::vector<std::vector<CoCoA::RingElem>>& generatorSets,
                 BitProp& bitProp)
{
  size_t k = generatorSets.size();
  std::vector<std::vector<CoCoA::RingElem>> newPolys(generatorSets);
  SplitGb2 splitBasis(k);
  do
  {
    // add newPolts to each basis
    for (size_t i = 0; i < k; ++i)
    {
      if (newPolys[i].size())
      {
        std::vector<CoCoA::RingElem> newGens{};

        const auto& basis = splitBasis[i].basis();
        std::copy(basis.begin(), basis.end(), std::back_inserter(newGens));
        std::copy(newPolys[i].begin(),
                  newPolys[i].end(),
                  std::back_inserter(newGens));
        splitBasis[i] = Gb(newGens);
        newPolys[i].clear();
      }
    }

    // compute polys that can be shared
    std::vector<CoCoA::RingElem> toPropagate{};
    for (size_t i = 0; i < k; ++i)
    {
      const auto& basis = splitBasis[i].basis();
      std::copy(basis.begin(), basis.end(), std::back_inserter(toPropagate));
      const auto extraProp = bitProp.getBitEqualities(splitBasis);
      std::copy(
          extraProp.begin(), extraProp.end(), std::back_inserter(toPropagate));
    }

    // share polys with ideals that accept them.
    for (const auto& p : toPropagate)
    {
      for (size_t j = 0; j < k; ++j)
      {
        if (admit(j, p) && !splitBasis[j].contains(p))
        {
          newPolys[j].push_back(p);
        }
      }
    }
  } while (std::any_of(newPolys.begin(), newPolys.end(), [](const auto& s) {
    return s.size();
  }));
  return splitBasis;
}

std::variant<std::vector<CoCoA::RingElem>, CoCoA::RingElem, bool>
splitZeroExtend(const std::vector<CoCoA::RingElem>& origPolys,
                const SplitGb2&& curBases,
                const PartialRoot&& curR,
                const BitProp& bitProp)
{
  Assert(origPolys.size());
  CoCoA::ring polyRing = CoCoA::owner(origPolys[0]);
  SplitGb2 bases(std::move(curBases));
  PartialRoot r(std::move(curR));
  long nAssigned = std::count_if(
      r.begin(), r.end(), [](const auto& v) { return v.has_value(); });
  if (std::any_of(bases.begin(), bases.end(), [](const Gb& i) {
        return i.isWholeRing();
      }))
  {
    for (const auto& p : origPolys)
    {
      auto value = cocoaEval(p, r);
      if (value.has_value() && !CoCoA::IsZero(*value) && !bases[0].contains(p))
      {
        return p;
      }
    }
    return false;
  }

  if (nAssigned == CoCoA::NumIndets(CoCoA::owner(origPolys[0])))
  {
    std::vector<CoCoA::RingElem> out;
    for (const auto& v : r)
    {
      out.push_back(*v);
    }
    return out;
  }
  auto brancher = applyRule(bases[0], polyRing, r);
  for (auto next = brancher->next(); next.has_value(); next = brancher->next())
  {
    long var = CoCoA::UnivariateIndetIndex(*next);
    Assert(var >= 0);
    CoCoA::RingElem val = -CoCoA::ConstantCoeff(*next);
    Assert(!r[var].has_value());
    PartialRoot newR = r;
    newR[var] = {val};
    Trace("ff::split::mc::debug")
        << std::string(1 + nAssigned, ' ') << CoCoA::indet(polyRing, var)
        << " = " << val << std::endl;
    std::vector<std::vector<CoCoA::RingElem>> newSplitGens{};
    for (const auto& b : bases)
    {
      newSplitGens.push_back({});
      std::copy(b.basis().begin(),
                b.basis().end(),
                std::back_inserter(newSplitGens.back()));
      newSplitGens.back().push_back(*next);
    }
    BitProp bitPropCopy = bitProp;
    SplitGb2 newBases = splitGb(newSplitGens, bitPropCopy);
    auto result = splitZeroExtend(
        origPolys, std::move(newBases), std::move(newR), bitPropCopy);
    if (!std::holds_alternative<bool>(result))
    {
      return result;
    }
  }
  return false;
}

std::optional<std::vector<CoCoA::RingElem>> splitFindZero(
    SplitGb2&& splitBasisIn, CoCoA::ring polyRing, BitProp& bitProp)
{
  SplitGb2 splitBasis = std::move(splitBasisIn);
  while (true)
  {
    std::vector<CoCoA::RingElem> allGens{};
    for (const auto& b : splitBasis)
    {
      std::copy(
          b.basis().begin(), b.basis().end(), std::back_inserter(allGens));
    }
    PartialRoot nullPartialRoot(CoCoA::NumIndets(polyRing));
    auto result = splitZeroExtend(
        allGens, SplitGb2(splitBasis), std::move(nullPartialRoot), bitProp);
    if (std::holds_alternative<CoCoA::RingElem>(result))
    {
      auto conflict = std::get<CoCoA::RingElem>(result);
      std::vector<std::vector<CoCoA::RingElem>> gens{};
      for (auto& b : splitBasis)
      {
        gens.push_back({});
        std::copy(b.basis().begin(),
                  b.basis().end(),
                  std::back_inserter(gens.back()));
        gens.back().push_back(conflict);
      }
      splitBasis = splitGb(gens, bitProp);
    }
    else if (std::holds_alternative<bool>(result))
    {
      return {};
    }
    else
    {
      return {std::get<std::vector<CoCoA::RingElem>>(result)};
    }
  }
}

Gb::Gb() : d_ideal(), d_basis(){};
Gb::Gb(const std::vector<CoCoA::RingElem>& generators)
    : d_ideal(), d_basis()
{
  if (generators.size())
  {
    d_ideal.emplace(CoCoA::ideal(generators));
    d_basis = CoCoA::GBasis(d_ideal.value());
  }
}

bool Gb::contains(const CoCoA::RingElem& p) const
{
  return d_ideal.has_value() && CoCoA::IsElem(p, d_ideal.value());
}
bool Gb::isWholeRing() const
{
  return d_ideal.has_value() && CoCoA::IsOne(d_ideal.value());
}
CoCoA::RingElem Gb::reduce(const CoCoA::RingElem& p) const
{
  return d_ideal.has_value() ? CoCoA::NF(p, d_ideal.value()) : p;
}
bool Gb::zeroDimensional() const
{
  return d_ideal.has_value() && CoCoA::IsZeroDim(d_ideal.value());
}
CoCoA::RingElem Gb::minimalPolynomial(const CoCoA::RingElem& var) const
{
  Assert(zeroDimensional());
  Assert(CoCoA::UnivariateIndetIndex(var) != -1);
  CoCoA::RingElem minPoly = CoCoA::MinPolyQuot(var, *d_ideal, var);
  return minPoly;
}
const std::vector<CoCoA::RingElem>& Gb::basis() const { return d_basis; }

BitProp::BitProp(const std::vector<Node>& facts, CocoaEncoder& encoder)
    : d_bits(), d_bitsums(encoder.bitsums()), d_enc(&encoder)
{
  for (const auto& fact : facts)
  {
    auto bs = parse::bitConstraint(fact);
    if (bs)
    {
      d_bits.insert(*bs);
    }
  }
}

BitProp::BitProp() : d_bits(), d_bitsums(), d_enc(nullptr) {}

std::vector<CoCoA::RingElem> BitProp::getBitEqualities(
    const std::vector<Gb>& splitBasis)
{
  std::vector<CoCoA::RingElem> output{};

  std::vector<Node> nonConstantBitsums{};
  for (const auto& bitsum : d_bitsums)
  {
    bool isConst = false;
    for (const auto& b : splitBasis)
    {
      CoCoA::RingElem normal = b.reduce(d_enc->getTermEncoding(bitsum));
      if (CoCoA::IsConstant(normal))
      {
        Integer val =
            d_enc->cocoaFfToFfVal(CoCoA::ConstantCoeff(normal)).getValue();
        if (val >= Integer(2).pow(bitsum.getNumChildren()))
        {
          output.clear();
          output.push_back(CoCoA::one(d_enc->polyRing()));
          return output;
        }
        for (size_t i = 0; i < bitsum.getNumChildren(); ++i)
        {
          auto bit = val.isBitSet(i) ? CoCoA::one(d_enc->polyRing())
                                     : CoCoA::zero(d_enc->polyRing());
          output.push_back(d_enc->getTermEncoding(bitsum[i]) - bit);
        }
        isConst = true;
        break;
      }
    }
    if (!isConst)
    {
      nonConstantBitsums.push_back(bitsum);
    }
  }

  for (size_t i = 0; i < nonConstantBitsums.size(); ++i)
  {
    for (size_t j = 0; j < i; ++j)
    {
      Node a = nonConstantBitsums[i];
      Node b = nonConstantBitsums[j];
      CoCoA::RingElem bsDiff =
          d_enc->getTermEncoding(a) - d_enc->getTermEncoding(b);
      if (std::any_of(
              splitBasis.begin(), splitBasis.end(), [&bsDiff](const auto& ii) {
                return ii.contains(bsDiff);
              }))
      {
        Trace("ffl::bitprop")
            << " (= " << a << "\n    " << b << ")" << std::endl;
        size_t min = std::min(a.getNumChildren(), b.getNumChildren());
        size_t max = std::max(a.getNumChildren(), b.getNumChildren());
        if (max > d_enc->size().d_val.length())
        {
          Trace("ffl::bitprop") << " bitsum overflow" << std::endl;
          continue;
        }
        bool allBits = true;
        for (const auto& sum : {a, b})
        {
          for (const auto& c : sum)
          {
            if (!d_bits.count(c))
            {
              CoCoA::RingElem p = d_enc->getTermEncoding(c);
              CoCoA::RingElem bitConstraint = p * p - p;
              if (std::any_of(splitBasis.begin(),
                              splitBasis.end(),
                              [&bitConstraint](const auto& ii) {
                                return ii.contains(bitConstraint);
                              }))
              {
                Trace("ffl::bitprop") << " bit through GB " << c << std::endl;
                d_bits.insert(c);
              }
            }
            if (!d_bits.count(c))
            {
              Trace("ffl::bitprop") << " non-bit " << c << std::endl;
              allBits = false;
            }
          }
        }

        if (!allBits) continue;

        for (size_t k = 0; k < min; ++k)
        {
          CoCoA::RingElem diff =
              d_enc->getTermEncoding(a[k]) - d_enc->getTermEncoding(b[k]);
          output.push_back(diff);
        }

        if (a.getNumChildren() != min || b.getNumChildren() != min)
        {
          Node n = b.getNumChildren() > min ? b : a;
          for (size_t k = min; k < max; ++k)
          {
            CoCoA::RingElem isZero = d_enc->getTermEncoding(n[k]);
            output.push_back(isZero);
          }
        }
      }
    }
  }
  return output;
}

bool admit(size_t i, const CoCoA::RingElem& p)
{
  Assert(i < 2);
  return CoCoA::deg(p) <= 1 && (i == 0 || CoCoA::NumTerms(p) <= 2);
}

std::optional<std::unordered_map<Node, FiniteFieldValue>> splitFindZero(
    const std::vector<Node>& facts, const FfSize& size)
{
  std::unordered_set<Node> bits{};
  CocoaEncoder enc(size);
  for (const auto& fact : facts)
  {
    enc.addFact(fact);
  }
  enc.endScan();
  for (const auto& fact : facts)
  {
    enc.addFact(fact);
  }

  std::vector<CoCoA::RingElem> nlGens = enc.polys();
  std::vector<CoCoA::RingElem> lGens = enc.bitsumPolys();
  for (const auto& p : enc.polys())
  {
    if (CoCoA::deg(p) <= 1)
    {
      lGens.push_back(p);
    }
  }

  BitProp bitProp(facts, enc);

  std::vector<std::vector<CoCoA::RingElem>> splitGens = {lGens, nlGens};
  SplitGb2 splitBasis = splitGb(splitGens, bitProp);
  if (std::any_of(splitBasis.begin(), splitBasis.end(), [](const auto& b) {
        return b.isWholeRing();
      }))
  {
    return {};
  }

  std::optional<std::vector<CoCoA::RingElem>> root =
      splitFindZero(std::move(splitBasis), enc.polyRing(), bitProp);
  if (root.has_value())
  {
    std::unordered_map<Node, FiniteFieldValue> model;
    for (const auto& [indetIdx, varNode] : enc.nodeIndets())
    {
      FiniteFieldValue literal = enc.cocoaFfToFfVal(root.value()[indetIdx]);
      Trace("ff::model") << "Model: " << varNode << " = " << literal
                         << std::endl;
      model.insert({varNode, literal});
    }
    return model;
  }
  else
  {
    return {};
  }
}

void checkModel(const SplitGb2& origBases,
                const std::vector<CoCoA::RingElem>& model)
{
#ifdef CVC5_ASSERTIONS
  for (const auto& b : origBases)
  {
    for (const auto& gen : b.basis())
    {
      auto value = cocoaEval(gen, model);
      if (!CoCoA::IsZero(value))
      {
        std::stringstream o;
        o << "Bad model!" << std::endl
          << "Generator " << gen << std::endl
          << "evaluated to " << value << std::endl
          << "under model: " << std::endl;
        for (size_t i = 0; i < model.size(); ++i)
        {
          o << " " << CoCoA::indet(CoCoA::owner(gen), i) << " -> " << model[i]
            << std::endl;
        }
        Assert(CoCoA::IsZero(value)) << o.str();
      }
    }
  }
#endif  // CVC5_ASSERTIONS
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
