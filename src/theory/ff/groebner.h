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
 * A configurably incremental groebner basis engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__GROEBNER_H
#define CVC5__THEORY__FF__GROEBNER_H

#include <CoCoA/RingFp.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/symbol.H>

#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/cdlist_forward.h"
#include "context/cdo.h"
#include "context/context.h"
#include "expr/node.h"
#include "theory/theory.h"
#include "theory/ff/trace.h"
#include "theory/ff/inc_trace.h"
#include "smt/env_obj.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

struct GroebnerResult {
  std::vector<CoCoA::RingElem> basis;
  std::vector<size_t> blame;
};

enum class Incrementality {
  // Bases are computed at full-effort, no bases are saved.
  None,
  // Bases are computed at full-effort, per-context bases are saved.
  Lazy,
  // Bases are computed at standard-effort, per-context bases are saved.
  Eager,
};

// Class for constructing a polynomial ideal for an incremental source of
// generators.
class IncrementalIdeal: EnvObj
{
 public:
  IncrementalIdeal(Env& env, CoCoA::ring polyRing);
  // Add new generators
  void pushGenerators(std::vector<CoCoA::RingElem>&& gens);
  // Is the ideal the whole ring?
  bool idealIsTrivial();
  // For a trivial ideal, return a (sub)list of generators that generate it.
  const std::vector<size_t>& trivialCoreIndices();
  // For a trivial ideal, return a (sub)list of generators that generate it.
  std::vector<CoCoA::RingElem> trivialCore();
  // For a non-trivial idea, check whether there is a base-field solution.
  bool hasSolution();
  // For a non-trivial idea with a base-field solution, get it.
  const std::vector<CoCoA::RingElem>& solution();
  // Remove the last batch of generators
  void pop();
 private:

  void ensureSolution();

  std::unique_ptr<context::Context> d_context;

  IncrementalTracer d_tracer{};
  context::CDList<CoCoA::RingElem> d_gens;
  context::CDO<std::vector<CoCoA::RingElem>> d_basis;
  context::CDO<bool> d_hasCore;
  context::CDO<std::vector<size_t>> d_core;
  context::CDO<std::optional<bool>> d_hasSolution;
  context::CDO<std::vector<CoCoA::RingElem>> d_solution;
};

class SubTheory : EnvObj, context::ContextNotifyObj
{
 public:
  // Create a new sub-theory.
  //
  // Parameters:
  // * env: 
  // * i: the level of incrementality.
  // * modulus: the size of this field for this theory, a prime.
  SubTheory(Env& env, Incrementality i, Integer modulus);

  // Notify this theory of a node it may need to handle.
  //
  // All nodes this theory sees in the future must be pre-registered.
  void preRegisterTerm(TNode);

  // Assert a fact to this theory.
  void notifyFact(TNode fact);

  // Check the current facts.
  void postCheck(Theory::Effort);

  // Has a conflict been detected?
  bool inConflict() const;

  // What is that conflict?
  const std::vector<Node>& conflict() const;

  // Get a model.
  const std::unordered_map<Node, Node>& model() const;

 private:

  // Called on SAT pop; we pop the incremental ideal if needed.
  void contextNotifyPop() override;

  // Compute a Groebner basis for the facts up to (not including) this index.
  void computeBasis(size_t factIndex);

  void extractModel();

  // Initialize the polynomial ring, set up post-registration data structures.
  void ensureInitPolyRing();

  // Translate t to CoCoA, and cache the result.
  void translate(TNode t);

  // Is registration done and the polynomial ring initialized?
  bool d_registrationDone();

  // Manages the incremental GB.
  std::optional<IncrementalIdeal> d_incrementalIdeal{};

  // For an atom x == y, contains the potential inverse of (x - y).
  //
  // Used to make x != y.
  std::unordered_map<Node, CoCoA::RingElem> d_atomInverses{};

  // Facts, in notification order.
  //
  // Uses SAT context.
  context::CDList<Node> d_facts;

  // The length of that fact list at each check.
  //
  // Uses SAT context.
  context::CDList<size_t> d_checkIndices;

  // The length of that fact list at each ideal update point.
  std::vector<size_t> d_updateIndices;

  // Non-empty if we're in a conflict.
  std::vector<Node> d_conflict{};

  // Cache from nodes to CoCoA polynomials.
  std::unordered_map<Node, CoCoA::RingElem> d_translationCache{};

  // A model, if we've found one. A map from variable nodes to their constant
  // values.
  std::unordered_map<Node, Node> d_model{};

  // Variables
  std::unordered_set<Node> d_vars{};

  // Variables
  std::unordered_map<size_t, Node> d_symbolIdxVars{};

  // Atoms
  std::unordered_set<Node> d_atoms{};

  Incrementality d_inc;
  CoCoA::ring d_baseRing;
  Integer d_modulus;
  // Set after registration is done.
  std::optional<CoCoA::ring> d_polyRing{};

};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__GROEBNER_H */
