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
 * Finite field rewriting machinery
 *
 * Summary of rewrites:
 * - negation
 *   - pre: change to scalar multiplication
 *   - post: un-needed because we rewrite away
 * - addition
 *   - pre: flatten
 *   - post: constant-fold
 *     - collect constants and sum
 *     - collect pairs (scalar, non-scalar) and sum scalars
 *     - trim identity
 * - multiplication
 *   - pre: flatten
 *   - post: constant-fold
 *     - collect constants and multiply
 *     - zero -> zero
 *     - trim identity
 */

#include "theory/arith/ff/rewriter.h"

#include <unordered_map>

#include "expr/algorithm/flatten.h"
#include "expr/node_manager.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

/** preRewrite negation */
Node preRewriteFfNeg(TNode t)
{
  Assert(t.getKind() == Kind::FINITE_FIELD_NEG);
  NodeManager* const nm = NodeManager::currentNM();
  const Node negOne = nm->mkConstFiniteFieldElem(Integer(-1), t.getType());
  return nm->mkNode(kind::FINITE_FIELD_MULT, negOne, t[0]);
}

/** preRewrite addition */
Node preRewriteFfAdd(TNode t)
{
  Assert(t.getKind() == Kind::FINITE_FIELD_ADD);
  return expr::algorithm::flatten(t);
}

/** postRewrite addition */
Node postRewriteFfAdd(TNode t)
{
  const TypeNode field = t.getType();
  Assert(field.isFiniteField());

  FiniteField one = FiniteField::mkOne(field.getFiniteFieldSize());

  FiniteField constantTerm = FiniteField::mkZero(field.getFiniteFieldSize());
  std::unordered_map<Node, FiniteField> scalarTerms;

  for (const auto& child : t)
  {
    if (child.isConst())
    {
      constantTerm = constantTerm + child.getConst<FiniteField>();
    }
    else
    {
      std::optional<std::pair<Node, FiniteField>> parsed = parseScalar(child);
      std::pair<Node, FiniteField> pair =
          parsed.value_or(std::make_pair(child, one));
      const auto entry = scalarTerms.find(pair.first);
      if (entry == scalarTerms.end())
      {
        scalarTerms.insert(pair);
      }
      else
      {
        entry->second = entry->second + pair.second;
      }
    }
  }
  NodeManager* const nm = NodeManager::currentNM();
  std::vector<Node> summands;
  if (scalarTerms.empty() || !constantTerm.getValue().isZero())
  {
    summands.push_back(nm->mkConst(constantTerm));
  }
  for (const auto& summand : scalarTerms)
  {
    Node c = nm->mkConst(summand.second);
    summands.push_back(expr::algorithm::flatten(
        nm->mkNode(Kind::FINITE_FIELD_MULT, c, summand.first)));
  }
  return mkNary(Kind::FINITE_FIELD_ADD, std::move(summands));
}

/** preRewrite multiplication */
Node preRewriteFfMult(TNode t)
{
  Assert(t.getKind() == Kind::FINITE_FIELD_MULT);
  return expr::algorithm::flatten(t);
}

/** postRewrite multiplication */
Node postRewriteFfMult(TNode t)
{
  const TypeNode field = t.getType();
  Assert(field.isFiniteField());

  FiniteField one = FiniteField::mkOne(field.getFiniteFieldSize());

  FiniteField constantTerm = FiniteField::mkOne(field.getFiniteFieldSize());
  std::vector<Node> summands;

  for (const auto& child : t)
  {
    if (child.isConst())
    {
      constantTerm = constantTerm * child.getConst<FiniteField>();
    }
    else
    {
      summands.push_back(child);
    }
  }
  NodeManager* const nm = NodeManager::currentNM();
  if (constantTerm.getValue().isZero())
  {
    summands.clear();
  }
  if (!constantTerm.getValue().isOne() || summands.empty())
  {
    summands.insert(summands.begin(), nm->mkConst(constantTerm));
  }
  return mkNary(Kind::FINITE_FIELD_MULT, std::move(summands));
}

/** Parse as a product with a constant scalar */
std::optional<std::pair<Node, FiniteField>> parseScalar(TNode t)
{
  if (t.getKind() == Kind::FINITE_FIELD_MULT && t[0].isConst())
  {
    std::vector<Node> restChildren(std::next(t.begin()), t.end());
    const Node rest = mkNary(Kind::FINITE_FIELD_MULT, std::move(restChildren));
    return {{rest, t[0].getConst<FiniteField>()}};
  }
  else
  {
    return {};
  }
}

Node mkNary(Kind k, std::vector<Node>&& children)
{
  Assert(children.size() > 0);
  if (children.size() == 1)
  {
    return children[0];
  }
  else
  {
    return NodeManager::currentNM()->mkNode(k, std::move(children));
  }
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
