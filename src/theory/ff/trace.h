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
 * Finite fields UNSAT trace construction
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__TRACE_H
#define CVC5__THEORY__FF__TRACE_H

#include <CoCoA/ring.H>
#include <CoCoA/TmpGPoly.H>

#include <unordered_map>
#include <unordered_set>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

class Tracer
{
 public:
  Tracer();
  void initFunctionPointers();
  void reset();
  void addInput(const CoCoA::RingElem& i);
  std::vector<size_t> trace(const CoCoA::RingElem& i) const;

 private:
  void sPoly(const CoCoA::GPoly* p, const CoCoA::GPoly* q, const CoCoA::GPoly* s);
  void reductionStart(const CoCoA::GPoly* p);
  void reductionStep(const CoCoA::GPoly* q);
  void reductionEnd(const CoCoA::GPoly* r);

  std::unordered_map<std::string, std::unordered_set<std::string>> d_graph{};
  std::unordered_map<std::string, size_t> d_inputs{};
  std::vector<std::string> d_reductionSeq{};
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__TRACE_H */
