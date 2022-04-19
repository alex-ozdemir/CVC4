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
 * Finite field rewriting machinery.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__FF__REWRITER_H
#define CVC5__THEORY__ARITH__FF__REWRITER_H

#include <optional>
#include <utility>

#include "expr/node.h"
#include "util/finite_field.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

/** preRewrite negation */
Node preRewriteFfNeg(TNode t);

/** preRewrite addition */
Node preRewriteFfAdd(TNode t);
/** postRewrite addition */
Node postRewriteFfAdd(TNode t);

/** preRewrite multiplication */
Node preRewriteFfMult(TNode t);
/** postRewrite multiplication */
Node postRewriteFfMult(TNode t);
/** Parse as a product with a constant scalar */
std::optional<std::pair<Node, FiniteField>> parseScalar(TNode t);

/** Make an n-ary operator of length is more than 1 */
Node mkNary(Kind k, std::vector<Node>&& children);

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal


#endif /* CVC5__THEORY__ARITH__FF__REWRITER_H */
