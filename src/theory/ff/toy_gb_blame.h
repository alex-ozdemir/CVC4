/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Kshitij Bansal
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Toy Groebner basis impl with blame-tracking.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__TOY_GB_BLAME_H
#define CVC5__THEORY__FF__TOY_GB_BLAME_H

#include <utility>

#include <CoCoA/PolyRing.H>
#include <CoCoA/SparsePolyOps-ideal.H>

namespace cvc5::internal {
namespace theory {
namespace ff {

/**
 * Compute a Groebner basis for the ideal I.
 *
 * Returns
 *
 * (1) the basis
 * (2) if the basis contains a constant: the indices of the generators of I that are to blame
 *     otherwise, and empty vector.
 */
std::pair<std::vector<CoCoA::RingElem>, std::vector<size_t>> toyGBasisBlame(CoCoA::ideal I);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__TOY_GB_BLAME_H */
