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
 * Toy Groebner basis impl.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__TOY_GB_H
#define CVC5__THEORY__FF__TOY_GB_H

#include "util/statistics_stats.h"

#include <CoCoA/PolyRing.H>
#include <CoCoA/SparsePolyOps-ideal.H>

namespace cvc5::internal {
namespace theory {
namespace ff {

std::vector<CoCoA::RingElem> toyGBasis(CoCoA::ideal I);

std::vector<CoCoA::RingElem> toyGBasisBlame(CoCoA::ideal I, std::vector<size_t>& blame);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__TOY_GB_H */
