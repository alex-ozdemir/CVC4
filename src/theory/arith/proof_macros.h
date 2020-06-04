/*********************                                                        */
/*! \file proof_macros.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Macros which run code when the old or new proof system is enabled,
 ** or unsat cores are enabled.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARITH__PROOF_MACROS_H
#define CVC4__THEORY__ARITH__PROOF_MACROS_H

#include "options/smt_options.h"

#ifdef CVC4_PROOF
#define ARITH_PROOF(x)                                      \
  if (CVC4::options::proof() || CVC4::options::unsatCores() \
      || CVC4::options::proofNew())                         \
  {                                                         \
    x;                                                      \
  }
#define ARITH_NULLPROOF(x)                               \
  (CVC4::options::proof() || CVC4::options::unsatCores() \
   || CVC4::options::proofNew())                         \
      ? x                                                \
      : NULL
#define ARITH_PROOF_ON()                                 \
  (CVC4::options::proof() || CVC4::options::unsatCores() \
   || CVC4::options::proofNew())
#else /* CVC4_PROOF */
#define ARITH_PROOF(x)
#define ARITH_NULLPROOF(x) NULL
#define ARITH_PROOF_ON() false
#endif /* CVC4_PROOF */

#endif  // CVC4__THEORY__ARITH__PROOF_MACROS_H
