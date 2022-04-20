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
 * Finite field utilities
 */

#include "theory/arith/ff/util.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

bool isFfAtom(TNode atom)
{
  if (atom.getKind() == Kind::EQUAL)
  {
    return atom[0].getType().isFiniteField();
  }
  else if (atom.getKind() == Kind::DISTINCT)
  {
    return atom[0].getType().isFiniteField();
  }
  else if (atom.getKind() == Kind::NOT && atom[0].getKind() == Kind::EQUAL)
  {
    return atom[0][0].getType().isFiniteField();
  }
  else
  {
    return false;
  }
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
