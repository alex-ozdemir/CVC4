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
 * CoCoA utilities
 */

#ifdef CVC5_USE_COCOA

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__COCOA_UTIL_H
#define CVC5__THEORY__FF__COCOA_UTIL_H

// external includes
#include <CoCoA/ring.H>

// std includes
#include <optional>
#include <vector>

// internal includes

namespace cvc5::internal {
namespace theory {
namespace ff {

using PartialRoot = std::vector<std::optional<CoCoA::RingElem>>;
using Root = std::vector<CoCoA::RingElem>;

/** partial evaluation of polynomials */
std::optional<CoCoA::RingElem> cocoaEval(
    CoCoA::RingElem poly,
    const std::vector<std::optional<CoCoA::RingElem>>& values);

/** total evaluation of polynomials */
CoCoA::RingElem cocoaEval(CoCoA::RingElem poly,
                          const std::vector<CoCoA::RingElem>& values);


}  // namespace theory
}  // namespace ff
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__COCOA_UTIL_H */

#endif /* CVC5_USE_COCOA */
