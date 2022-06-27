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
 * Finite fields theory
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__THEORY_FF_H
#define CVC5__THEORY__FF__THEORY_FF_H

#include <memory>

#include "context/cdlist_forward.h"
#include "context/cdo.h"
#include "smt/logic_exception.h"
#include "theory/care_pair_argument_callback.h"
#include "theory/ff/theory_ff_rewriter.h"
#include "theory/theory.h"
#include "theory/theory_eq_notify.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_state.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

class TheoryFiniteFields : public Theory
{
 public:
  /** Constructs a new instance of TheoryFiniteFields w.r.t. the provided
   * contexts. */
  TheoryFiniteFields(Env& env, OutputChannel& out, Valuation valuation);
  ~TheoryFiniteFields() override;

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override;
  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  /** finish initialization */
  void finishInit() override;
  //--------------------------------- end initialization

  //--------------------------------- standard check
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort level) override;
  /** Notify fact */
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  //--------------------------------- end standard check
  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  void computeCareGraph() override;
  TrustNode explain(TNode) override;
  Node getModelValue(TNode) override;
  std::string identify() const override { return "THEORY_FF"; }
  void preRegisterTerm(TNode node) override;
  /**
   * If the ff-ext option is not set and we have an extended operator,
   * we throw an exception. Additionally, we expand operators like choose
   * and is_singleton.
   */
  TrustNode ppRewrite(TNode n, std::vector<SkolemLemma>& lems) override;
  PPAssertStatus ppAssert(TrustNode tin,
                          TrustSubstitutionMap& outSubstitutions) override;
  void presolve() override;
  bool isEntailed(Node n, bool pol);

 private:
  // Returns a boolean indicating whether d_ffFacts are satisfiable.
  bool isSat();

  bool isSat(const std::vector<Node>& assertions, bool constructModel);

  TheoryFiniteFieldsRewriter d_rewriter{};

  /** The state of the ff solver at full effort */
  TheoryState d_state;

  /** The inference manager */
  TheoryInferenceManager d_im;

  /** Manages notifications from our equality engine */
  TheoryEqNotifyClass d_eqNotify;

  // facts
  context::CDList<Node> d_ffFacts;

  // The solution, if we've found one. A map from variable nodes to their
  // constant values.
  context::CDO<std::unordered_map<Node, Node>> d_solution;

  struct Statistics
  {
    // Number of groebner-basis reductions
    IntStat d_numReductions;
    // Time spent in groebner-basis reductions
    TimerStat d_reductionTime;
    // Time spent in model script
    TimerStat d_modelScriptTime;
    Statistics(StatisticsRegistry& reg, const std::string& prefix);
  };

  Statistics d_stats;
}; /* class TheoryFiniteFields */

std::unordered_set<Node> getVars(const std::vector<Node>& terms);

std::unordered_set<Integer, IntegerHashFunction> getFieldSizes(
    const std::vector<Node>& terms);

size_t countDisequalities(const std::vector<Node>& terms);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__THEORY_FF_H */
