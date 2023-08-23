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
 * utilities
 */

#include "theory/ff/util.h"

// external includes

// std includes

// internal includes
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

FieldObj::FieldObj(const FfSize& size)
    : d_size(size),
      d_nm(NodeManager::currentNM()),
      d_zero(d_nm->mkConst(FiniteFieldValue(0, d_size))),
      d_one(d_nm->mkConst(FiniteFieldValue(1, d_size)))
{
}

Node FieldObj::mkAdd(std::vector<Node>&& summands)
{
  if (summands.empty())
  {
    return d_zero;
  }
  else if (summands.size() == 1)
  {
    return summands[0];
  }
  else
  {
    return d_nm->mkNode(kind::FINITE_FIELD_ADD, std::move(summands));
  }
}

Node FieldObj::mkMul(std::vector<Node>&& factors)
{
  if (factors.empty())
  {
    return d_one;
  }
  else if (factors.size() == 1)
  {
    return factors[0];
  }
  else
  {
    return d_nm->mkNode(kind::FINITE_FIELD_MULT, std::move(factors));
  }
}

bool isFfLeaf(const Node& n)
{
  return Theory::isLeafOf(n, THEORY_FF);
}

bool isFfTerm(const Node& n)
{
  return n.getType().isFiniteField();
}

bool isFfFact(const Node& n)
{
  return (n.getKind() == kind::EQUAL && n[0].getType().isFiniteField())
         || (n.getKind() == kind::NOT && n[0].getKind() == kind::EQUAL
             && n[0][0].getType().isFiniteField());
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
