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

#include "util/cocoa_globals.h"

#ifdef CVC5_USE_COCOA
#include <CoCoA/GlobalManager.H>
#endif /* CVC5_USE_COCOA */

namespace cvc5::internal {

void initCocoaGlobalManager()
{
#ifdef CVC5_USE_COCOA
  if (s_cocoaGlobalManager == nullptr)
  {
    s_cocoaGlobalManager = new CoCoA::GlobalManager();
  }
#endif /* CVC5_USE_COCOA */
}

}  // namespace cvc5::internal
