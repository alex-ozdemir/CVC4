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
 * Singleton CoCoA global manager
 */

#include "cvc5_public.h"

#ifndef CVC5__UTIL__COCOA_GLOBALS_H
#define CVC5__UTIL__COCOA_GLOBALS_H

#ifdef CVC5_USE_COCOA
#include <CoCoA/GlobalManager.H>
#endif /* CVC5_USE_COCOA */

namespace cvc5::internal {

#ifdef CVC5_USE_COCOA
[[maybe_unused]] static CoCoA::GlobalManager* s_cocoaGlobalManager = nullptr;
#endif /* CVC5_USE_COCOA */

/**
 * Intializes the CoCoA global manager if
 *    (a) CoCoA was enabled in this build and
 *    (b) it has not been intialized already
 */
void initCocoaGlobalManager();

}  // namespace cvc5::internal

#endif /* CVC5__UTIL__COCOA_GLOBALS_H */
