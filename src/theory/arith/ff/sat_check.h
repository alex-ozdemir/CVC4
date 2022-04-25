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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__FF__SAT_CHECK_H
#define CVC5__THEORY__ARITH__FF__SAT_CHECK_H

#include <unordered_set>

#include "context/cdlist_forward.h"
#include "expr/node.h"
#include "util/integer.h"
#include "util/finite_field.h"

#include <CoCoA/library.H>

namespace cvc5::internal {
namespace theory {
namespace arith {

/** Is this a finite-field atom? */
bool isSat(const context::CDList<Node>& assertions);

std::unordered_set<Node> getVars(const context::CDList<Node>& terms);

std::unordered_set<Integer, IntegerHashFunction> getFieldSizes(const context::CDList<Node>& terms);

size_t countDisequalities(const context::CDList<Node>& terms);

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal


#endif /* CVC5__THEORY__ARITH__FF__SAT_CHECK_H */
