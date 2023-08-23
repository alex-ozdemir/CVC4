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
#include <queue>
#include <unordered_map>

// internal includes
#include "base/output.h"
#include "expr/attribute.h"
#include "expr/node.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

namespace parse {

/** Characterization of a univariate, degree <= 2 polynomial */
struct Spectrum
{
  /** the variable; ignore if degree is 0 */
  Node var;
  /** the degree in {0, 1, 2} */
  uint8_t degree;
  /** value at 0 */
  FiniteFieldValue val0;
  /** value at 1 */
  FiniteFieldValue val1;
};

using SpectrumOpt = std::optional<Spectrum>;

/**
 * Perform computations needed to check whether t is part of a bit-constraint.
 * @param t a field term
 * @param depth how deep to search in term before concluding that this is not a
 * bit-constraint
 * @return none if t is too deep or mulitvariate, otherwise, a Spectrum.
 */
SpectrumOpt spectrum(const Node& t, uint8_t depth = 5);

/**
 * Detect whether this node constrains a variable to 0.
 * @param fact a node asserted to FF
 */
bool zeroConstraint(const Node& fact);

/**
 * Detect whether this node constrains a variable to 1.
 * @param fact a node asserted to FF
 */
bool oneConstraint(const Node& fact);

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
 * Detect whether this node is a sum of affine monomials
 *
 * @param t a potential affine funciton
 * @return a constant and
 *         a map from variables to scalars
 */
std::optional<
    std::pair<FiniteFieldValue, std::unordered_map<Node, FiniteFieldValue>>>
sumAffineMonomial(const Node& t);

/**
 * Detect whether this node is a linear equality
 *
 * @param t a potential linear equality
 * @return a map from variables to scalars, encoding a sum that must be zero.
 */
std::optional<std::unordered_map<Node, FiniteFieldValue>> linearEq(
    const Node& t);

/**
 * Detect whether this node is an affine equality
 *
 * @param t a potential linear equality
 * @return a constant and
 *         a map from variables to scalars, encoding a sum that must be zero.
 */
std::optional<
    std::pair<FiniteFieldValue, std::unordered_map<Node, FiniteFieldValue>>>
affineEq(const Node& t);

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
 * Detect whether this node is an affine sum of terms that do not have other
 * uses.
 *
 * @param t a potential affine sum
 * @param hasOtherUses node predicate for whether there are other uses
 * @return the linear monomials
 *         everything else in the sum
 */
template <class HasOtherUses>
std::optional<
    std::pair<std::unordered_map<Node, FiniteFieldValue>, std::vector<Node>>>
affineSum(const Node& t, HasOtherUses hasOtherUses)
{
  TypeNode ty = t.getType();
  if (!ty.isFiniteField())
  {
    return {};
  }
  if (t.getKind() != kind::FINITE_FIELD_ADD)
  {
    return {};
  }
  std::unordered_map<Node, FiniteFieldValue> monomials{};
  std::vector<Node> otherSummands{};

  for (const Node& summand : t)
  {
    if (!hasOtherUses(summand))
    {
      auto monomial = linearMonomial(summand);
      if (monomial.has_value())
      {
        monomials.insert(std::move(monomial.value()));
        continue;
      }
    }

    otherSummands.push_back(summand);
  }

  return {{std::move(monomials), std::move(otherSummands)}};
}

/**
 * Given a sum s1 + ... + sN, extract sub-sums of form k * (x0 + 2*x1 + 4*x2 +
 * ... 2^I*xI), where each xJ passes the predicate isBit.
 *
 * @param t a potential bitsum
 * @param isBit node predicate that indicates whether a variable is
 * bitConstrained
 * @param hasOtherUses node predicate for whether there are other uses
 * @return the bitsums (k, {xJ})
 *         everything else in the sum
 */
template <class IsBit, class HasOtherUses>
std::optional<
    std::pair<std::vector<std::pair<FiniteFieldValue, std::vector<Node>>>,
              std::vector<Node>>>
bitSums(const Node& t, IsBit isBit, HasOtherUses hasOtherUses)
{
  auto nm = NodeManager::currentNM();
  auto res = affineSum(t, hasOtherUses);
  if (!res.has_value())
  {
    return {};
  }
  TypeNode ty = t.getType();
  const Integer& size = ty.getFfSize();
  auto& [monomials, rest] = res.value();
  Trace("ff::parse::debug") << "bitSums start" << std::endl;

  std::unordered_map<FiniteFieldValue, Node, FiniteFieldValueHashFunction>
      bitMonomials{};
  std::unordered_set<FiniteFieldValue, FiniteFieldValueHashFunction>
      monomialCoeffs{};
  std::priority_queue<std::pair<Integer, FiniteFieldValue>> q{};
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
    else
    {
      q.emplace(-coeff.toSignedInteger().abs(), coeff);
      Trace("ff::parse::debug")
          << "bitMonomial " << coeff << " " << var << std::endl;
    }
  }

  std::vector<std::pair<FiniteFieldValue, std::vector<Node>>> bitSums{};
  // TODO: consider other starting constants. Especially to handle gaps...
  FiniteFieldValue two(2, size);
  // look for runs k*x, 2k*y, 4k*z, ...
  while (!q.empty())
  {
    FiniteFieldValue k = q.top().second;
    q.pop();
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

/**
 * Extract linear monomials.
 *
 * @param t a potential affine sum
 * @param hasOtherUses node predicate for whether there are other uses
 * @return the linear monomials
 *         everything else in the sum
 */
std::optional<std::pair<std::vector<std::pair<Node, FiniteFieldValue>>,
                        std::vector<Node>>>
extractLinearMonomials(const Node& t);

/**
 * Given a sum s1 + ... + sN, extract sub-sums of form k * (x0 + 2*x1 + 4*x2 +
 * ... 2^I*xI), where each xJ passes the predicate isBit.
 *
 * @param t a potential bitsum
 * @param isBit node set containing bit-constrained vars; these are prefered in
 *              bitsum extraction.
 * @return the bitsums (k, {xJ})
 *         everything else in the sum
 */
std::optional<
    std::pair<std::vector<std::pair<FiniteFieldValue, std::vector<Node>>>,
              std::vector<Node>>>
bitSums(const Node& t, std::unordered_set<Node> isBit);

/**
 * Is this a disjunctive bit constraint (or (= x 0) (= x 1))?
 *
 * @param t a fact
 * @return the var that is bit-constrained
 */
std::optional<Node> disjunctiveBitConstraint(const Node& t);

}  // namespace parse

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__PARSE_H */
