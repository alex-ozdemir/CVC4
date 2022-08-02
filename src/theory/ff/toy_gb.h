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
 * Toy Groebner basis implementation. Included because Buchberger's algorithm
 * is historically important, and it can be informative to run experiments
 * against it.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__TOY_GB_H
#define CVC5__THEORY__FF__TOY_GB_H

#include <CoCoA/PolyRing.H>
#include <CoCoA/SparsePolyOps-ideal.H>

namespace cvc5::internal {
namespace theory {
namespace ff {

/**
 * Compute a Groebner basis for the ideal I.
 *
 * Uses Buchberger's algorithm, more or less.
 *
 * Does not produce a reduced Groebner basis, but if the ideal is trivial, we
 * guarantee that the basis will be [1].
 */
std::vector<CoCoA::RingElem> toyGBasis(CoCoA::ideal I);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__TOY_GB_H */

