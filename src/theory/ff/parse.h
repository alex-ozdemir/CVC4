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
 * @param t a potential bit-sum
 * @return the sum, followed by the bits (LSB at index 0)
 */
std::optional<std::pair<Node, std::vector<Node>>> bitsConstraint(const Node& fact);

}  // namespace parse

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__PARSE_H */
