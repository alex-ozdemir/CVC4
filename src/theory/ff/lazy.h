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
 * lazy solver
 */

#ifdef CVC5_USE_COCOA

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__LAZY_H
#define CVC5__THEORY__FF__LAZY_H

// external includes

// std includes

// internal includes
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/ff/util.h"
#include "util/finite_field_value.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

class LazySolver : EnvObj, FieldObj
{
 public:
  LazySolver(Env& env, const FfSize& size);
  void assertFact(TNode fact);
  void check();
  Result result() const { return d_result; }
  const std::unordered_map<Node, FiniteFieldValue>& model() const
  {
    return d_model;
  }
  void clear();

 private:
  Result d_result{Result::UNKNOWN};
  std::unordered_map<Node, FiniteFieldValue> d_model{};
  std::vector<Node> d_facts{};
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__LAZY_H */

#endif /* CVC5_USE_COCOA */
