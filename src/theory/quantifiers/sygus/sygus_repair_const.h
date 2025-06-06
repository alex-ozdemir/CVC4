/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * sygus_repair_const
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H

#include <unordered_set>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class Env;
class LogicInfo;

namespace theory {
namespace quantifiers {

class QuantifiersInferenceManager;
class TermDbSygus;

/** SygusRepairConst
 *
 * This module is used to repair portions of candidate solutions. In particular,
 * given a synthesis conjecture:
 *   exists f. forall x. P( f, x )
 * and a candidate solution f = \x. t[x,r] where r are repairable terms, this
 * function checks whether there exists a term of the form \x. t[x,c'] for some
 * constants c' such that:
 *   forall x. P( (\x. t[x,c']), x )  [***]
 * is satisfiable, where notice that the above formula after beta-reduction may
 * be one in pure first-order logic in a decidable theory (say linear
 * arithmetic). To check this, we invoke a separate instance of the SolverEngine
 * within repairSolution(...) below, which if satisfiable gives us the
 * valuation for c'.
 */
class SygusRepairConst : protected EnvObj
{
 public:
  SygusRepairConst(Env& env,
                   QuantifiersInferenceManager& qim,
                   TermDbSygus* tds);
  ~SygusRepairConst() {}
  /** initialize
   *
   * Initialize this class with the base instantiation (body) of the sygus
   * conjecture (see SynthConjecture::d_base_inst) and its candidate variables
   * (see SynthConjecture::d_candidates).
   */
  void initialize(Node base_inst, const std::vector<Node>& candidates);
  /** repair solution
   *
   * This function is called when candidates -> candidate_values is a (failed)
   * candidate solution for the synthesis conjecture.
   *
   * If this function returns true, then this class adds to repair_cv the
   * repaired version of the solution candidate_values for each candidate,
   * where for each index i, repair_cv[i] is obtained by replacing constant
   * subterms in candidate_values[i] with others, and
   *    candidates -> repair_cv
   * is a solution for the synthesis conjecture associated with this class.
   * Moreover, it is the case that
   *    repair_cv[j] != candidate_values[j], for at least one j.
   * We always consider applications of the "any constant" constructors in
   * candidate_values to be repairable.
   * The repaired solution has the property that it satisfies the synthesis
   * conjecture whose body is given by sygusBody.
   */
  bool repairSolution(Node sygusBody,
                      const std::vector<Node>& candidates,
                      const std::vector<Node>& candidate_values,
                      std::vector<Node>& repair_cv);
  /**
   * Same as above, but where sygusBody is the body (base_inst) provided to the
   * call to initialize of this class.
   */
  bool repairSolution(const std::vector<Node>& candidates,
                      const std::vector<Node>& candidate_values,
                      std::vector<Node>& repair_cv);
  /**
   * Return whether this module has the possibility to repair solutions. This is
   * true if this module has been initialized, and at least one candidate has
   * an "any constant" constructor.
   */
  bool isActive() const;
  /** must repair?
   *
   * This returns true if n must be repaired for it to be a valid solution.
   * This corresponds to whether n contains a subterm that is a symbolic
   * constructor like the "any constant" constructor.
   */
  static bool mustRepair(Node n);

 private:
  /** Reference to the quantifiers inference manager */
  QuantifiersInferenceManager& d_qim;
  /** pointer to the sygus term database of d_qe */
  TermDbSygus* d_tds;
  /**
   * The "base instantiation" of the deep embedding form of the synthesis
   * conjecture associated with this class, see CegConjecture::d_base_inst.
   */
  Node d_base_inst;
  /**
   * whether any sygus type for the candidate variables of d_base_inst (the
   * syntactic restrictions) allows all constants. If this flag is false, then
   * this class is a no-op.
   */
  bool d_allow_constant_grammar;
  /** a cache of satisfiability queries of the form [***] above we have tried */
  std::unordered_set<Node> d_queries;
  /** The queries that were unsat */
  std::unordered_set<Node> d_unsatQueries;
  /**
   * Register information for sygus type tn, tprocessed stores the set of
   * already registered types.
   */
  void registerSygusType(TypeNode tn, std::map<TypeNode, bool>& tprocessed);
  /** is repairable?
   *
   * This returns true if n can be repaired by this class. In particular, we
   * return true if n is an "any constant" constructor.
   */
  static bool isRepairable(Node n);
  /** get skeleton
   *
   * Returns a skeleton for sygus datatype value n, where the subterms of n that
   * are repairable are replaced by free variables. Since we are interested in
   * returning canonical skeletons, the free variables we use in this
   * replacement are taken from TermDbSygus, where we track indices
   * in free_var_count. Variables we introduce in this way are added to sk_vars.
   * The mapping sk_vars_to_subs contains entries v -> c, where v is a
   * variable in sk_vars, and c is the term in n that it replaced.
   */
  Node getSkeleton(Node n,
                   std::map<TypeNode, size_t>& free_var_count,
                   std::vector<Node>& sk_vars);
  /** get first-order query
   *
   * This function returns a formula that is equivalent to the negation of the
   * synthesis conjecture whose body is given in the first argument, where
   * candidates are replaced by candidate_skeletons,
   * whose free variables are in the set sk_vars. The returned formula
   * is a first-order (quantified) formula in the background logic, without UF,
   * of the form [***] above.
   */
  Node getFoQuery(Node body,
                  const std::vector<Node>& candidates,
                  const std::vector<Node>& candidate_skeletons,
                  const std::vector<Node>& sk_vars);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS_REPAIR_CONST_H */
