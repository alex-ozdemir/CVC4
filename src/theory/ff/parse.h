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
 * parsing structured field terms
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__PARSE_H
#define CVC5__THEORY__FF__PARSE_H

// external includes

// std includes
#include <optional>
#include <unordered_map>

// internal includes
#include "expr/node.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

namespace parse {

/**
 * Detect whether this node is a squared variable
 * @param t a potential FF square
 * @return the variable (unsquared), if this is a square.
 */
std::optional<Node> square(const Node& t);

/**
 * Detect whether this node has form (x - 1)
 * @param t a node
 * @return the variable x, if t matches the pattern
 */
std::optional<Node> xMinusOne(const Node& t);

/**
 * Detect whether this node has form (ff.mul x (x - 1)) (or equivalent)
 * @param t a node
 * @return the variable x if t matches the pattern
 */
std::optional<Node> xXMinusOne(const Node& t);

/**
 * Detect whether this node is a bit-constraint.
 * @param fact a node asserted to FF
 * @return a variable that is bit-constrained by this fact, if this fact is a
 *         bit constraint.
 */
std::optional<Node> bitConstraint(const Node& fact);

/** Detect whether this node says that a variable is not equal to a constant.
 * @param fact a node asserted to FF
 * @return a variable that is not equal to this value.
 */
std::optional<std::pair<Node, FiniteFieldValue>> varNeValue(const Node& fact);

/**
 * Detect whether this node is a variable multiplied by a scalar:
 *
 *    * k * X
 *    * X * k
 *    * X
 *    * -X
 *
 * @param t a potential linear monomial
 * @return the variable and scalar
 */
std::optional<std::pair<Node, FiniteFieldValue>> linearMonomial(const Node& t);

/**
 * Detect whether this node is a sum of linear monomials
 *
 * @param t a potential linear funciton
 * @return a map from variables to scalars
 */
std::optional<std::unordered_map<Node, FiniteFieldValue>> sumLinearMonomial(
    const Node& t);

/**
 * Detect whether this node is a linear equality
 *
 * @param t a potential linear equality
 * @return a map from variables to scalars, encoding a sum that must be zero.
 */
std::optional<std::unordered_map<Node, FiniteFieldValue>> linearEq(
    const Node& t);

/**
 * For a linear map in N variables, ensure that at least N/2 have positive
 * coefficients, possible by negating the map.
 */
void normalizeLinearEq(std::unordered_map<Node, FiniteFieldValue>& linearEq);

/**
 * Detect whether this node enforces a bit-sum.
 *
 * For example:
 *   -> x0 + 2 * x1 + 4 * x2 + ... 2^N * xN = y
 *   -> x0 + 2 * x1 + 4 * x2 + ... 2^N * xN - y = 0
 *   -> -x0 + -2 * x1 + -4 * x2 + ... -2^N * xN + y = 0
 *   -> -1 * x0 + -2 * x1 + -4 * x2 + ... -2^N * xN = - y
 *
 * Only parses if the variables are all distinct.
 *
 * @param t a potential bit-sum
 * @return the sum, followed by the bits (LSB at index 0)
 */
std::optional<std::pair<Node, std::vector<Node>>> bitsConstraint(
    const Node& fact);

/**
 * Detect whether this node is an affine sum
 *
 * @param t a potential affine sum
 * @return the linear monomials
 *         everything else in the sum
 */
std::optional<
    std::pair<std::unordered_map<Node, FiniteFieldValue>, std::vector<Node>>>
affineSum(const Node& t);

/**
 * Given a sum s1 + ... + sN, extract sub-sums of form k * (x0 + 2*x1 + 4*x2 +
 * ... 2^I*xI), where each xJ passes the predicate isBit.
 *
 * @param t a potential bitsum
 * @return the bitsums (k, {xJ})
 *         everything else in the sum
 */
template <class IsBit>
std::optional<
    std::pair<std::vector<std::pair<FiniteFieldValue, std::vector<Node>>>,
              std::vector<Node>>>
bitSums(const Node& t, IsBit isBit)
{
  auto nm = NodeManager::currentNM();
  auto res = affineSum(t);
  if (!res.has_value())
  {
    return {};
  }
  TypeNode ty = t.getType();
  const Integer& size = ty.getFfSize();
  auto& [monomials, rest] = res.value();

  std::unordered_map<FiniteFieldValue, Node, FiniteFieldValueHashFunction>
      bitMonomials{};
  std::unordered_set<FiniteFieldValue, FiniteFieldValueHashFunction>
      monomialCoeffs{};
  for (const auto& [var, coeff] : monomials)
  {
    monomialCoeffs.insert(coeff);
    bool inBitMonomialMap = false;
    if (isBit(var))
    {
      inBitMonomialMap = bitMonomials.insert({coeff, var}).second;
    }
    if (!inBitMonomialMap)
    {
      rest.push_back(
          nm->mkNode(kind::FINITE_FIELD_MULT, nm->mkConst(coeff), var));
    }
  }

  std::vector<std::pair<FiniteFieldValue, std::vector<Node>>> bitSums{};
  // TODO: consider other starting constants. Especially to handle gaps...
  std::vector<FiniteFieldValue> startConsts = {{1, size}, {-1, size}};
  FiniteFieldValue two(2, size);
  // look for runs k*x, 2k*y, 4k*z, ...
  for (size_t i = 0; i < startConsts.size(); ++i)
  {
    FiniteFieldValue k = startConsts[i];
    FiniteFieldValue acc = k;
    std::vector<Node> bits{};
    std::vector<Node> erasedSummands{};
    while (bitMonomials.count(acc))
    {
      auto var = bitMonomials.at(acc);
      bits.push_back(var);
      erasedSummands.push_back(
          nm->mkNode(kind::FINITE_FIELD_MULT, nm->mkConst(acc), var));
      bitMonomials.erase(acc);
      acc *= two;
    }
    if (monomialCoeffs.count(acc))
    {
      monomialCoeffs.erase(acc);
      startConsts.push_back(two * acc);
    }
    if (bits.size() > 1)
    {
      bitSums.emplace_back(k, std::move(bits));
    }
    else
    {
      for (auto& summand : erasedSummands)
      {
        rest.push_back(std::move(summand));
      }
    }
  }

  for (const auto& [coeff, var] : bitMonomials)
  {
    rest.push_back(
        nm->mkNode(kind::FINITE_FIELD_MULT, nm->mkConst(coeff), var));
  }
  return {{std::move(bitSums), std::move(rest)}};
}

}  // namespace parse

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__PARSE_H */
