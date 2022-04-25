/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Finite field satisfiability checking
 */

#include "theory/arith/ff/sat_check.h"

#include <CoCoA/library.H>

#include <numeric>
#include <unordered_map>

#include "context/cdlist.h"
#include "expr/node_manager_attributes.h"
#include "expr/node_traversal.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

/** Is this a finite-field atom? */
bool isSat(const context::CDList<Node>& assertions)
{
  std::unordered_set<Node> vars = getVars(assertions);
  std::unordered_set<Integer, IntegerHashFunction> sizes =
      getFieldSizes(assertions);
  if (TraceIsOn("arith::ff"))
  {
    Trace("arith::ff") << "Vars: " << std::endl;
    for (const auto& v : vars)
    {
      Trace("arith::ff") << " - " << v << std::endl;
    }
    Trace("arith::ff") << "Sizes: " << std::endl;
    for (const auto& v : sizes)
    {
      Trace("arith::ff") << " - " << v << std::endl;
    }
  }
  AlwaysAssert(sizes.size() == 1)
      << "Unsupported: multiple field sizes. See arith::ff channel.";
  CoCoA::BigInt size = CoCoA::BigIntFromString(sizes.begin()->toString());
  CoCoA::QuotientRing ringFp = CoCoA::NewZZmod(size);
  std::vector<Node> nodes;
  std::vector<CoCoA::symbol> symbolVec;
  for (const auto& var : vars)
  {
    CoCoA::symbol sym(var.getAttribute(expr::VarNameAttr()));
    symbolVec.push_back(sym);
    nodes.push_back(var);
  }
  CoCoA::SparsePolyRing ringPoly = CoCoA::NewPolyRing(ringFp, symbolVec);
  std::unordered_map<Node, CoCoA::RingElem> varPolys;
  for (long i = 0; i < CoCoA::NumIndets(ringPoly); ++i)
  {
    CoCoA::RingElem poly = CoCoA::indet(ringPoly, i);
    varPolys.insert(std::make_pair(nodes[i], poly));
  }
  std::unordered_map<Node, CoCoA::RingElem> nodePolys(varPolys);
  for (const auto& term : assertions)
  {
    for (const auto& node :
         NodeDfsIterable(term, VisitOrder::POSTORDER, [&nodePolys](TNode nn) {
           return nodePolys.count(nn) > 0;
         }))
    {
      if (node.getType().isFiniteField())
      {
        CoCoA::RingElem poly;
        std::vector<CoCoA::RingElem> subPolys;
        std::transform(node.begin(),
                       node.end(),
                       std::back_inserter(subPolys),
                       [&nodePolys](Node n) { return nodePolys[n]; });
        switch (node.getKind())
        {
          case Kind::FINITE_FIELD_ADD:
            poly = std::accumulate(
                subPolys.begin(),
                subPolys.end(),
                CoCoA::RingElem(ringPoly->myZero()),
                [](CoCoA::RingElem a, CoCoA::RingElem b) { return a + b; });
            break;
          case Kind::FINITE_FIELD_NEG: poly = -subPolys[0]; break;
          case Kind::FINITE_FIELD_MULT:
            poly = std::accumulate(
                subPolys.begin(),
                subPolys.end(),
                CoCoA::RingElem(ringPoly->myOne()),
                [](CoCoA::RingElem a, CoCoA::RingElem b) { return a * b; });
            break;
          case Kind::CONST_FINITE_FIELD:
          {
            CoCoA::BigInt constant = CoCoA::BigIntFromString(
                node.getConst<FiniteField>().getValue().toString());
            poly = ringPoly->myOne() * constant;
            break;
          }
          default:
            Unreachable() << "Invalid finite field kind: " << node.getKind();
        }
        Trace("arith::ff") << "Translated " << node << "\t-> " << poly
                           << std::endl;
        nodePolys.insert(std::make_pair(node, poly));
      }
    }
  }
  std::vector<CoCoA::RingElem> generators;
  for (const auto& assertion : assertions)
  {
    switch (assertion.getKind())
    {
      case Kind::EQUAL:
        generators.push_back(nodePolys[assertion[0]] - nodePolys[assertion[1]]);
        break;
      case Kind::DISTINCT: Unhandled() << "diseq in ff SAT"; break;
      default:
        Unhandled() << "Kind " << assertion.getKind()
                    << " in finite field sat check";
    }
  }
  CoCoA::ideal ideal = CoCoA::ideal(generators);
  const auto basis = CoCoA::GBasis(ideal);
  Trace("arith::ff") << "Groebner basis " << basis << std::endl;
  for (const auto& basisPoly : basis)
  {
    if (CoCoA::deg(basisPoly) == 0)
    {
      return false;
    }
  }

  return true;
}

std::unordered_set<Node> getVars(const context::CDList<Node>& terms)
{
  std::unordered_set<Node> vars;
  for (const auto& term : terms)
  {
    for (const auto& node : NodeDfsIterable(term))
    {
      if (node.isVar())
      {
        vars.insert(node);
      }
    }
  }
  return vars;
}

std::unordered_set<Integer, IntegerHashFunction> getFieldSizes(
    const context::CDList<Node>& terms)
{
  std::unordered_set<Integer, IntegerHashFunction> sizes = {};
  for (const auto& term : terms)
  {
    for (const auto& node : NodeDfsIterable(term))
    {
      TypeNode ty = node.getType();
      if (ty.isFiniteField())
      {
        sizes.insert(ty.getFiniteFieldSize());
      }
    }
  }
  return sizes;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
