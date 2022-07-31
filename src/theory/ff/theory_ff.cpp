/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Kshitij Bansal
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

#include "theory/ff/theory_ff.h"

#include <CoCoA/library.H>

#include <cerrno>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <unordered_map>

#include "expr/node_manager_attributes.h"
#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"
#include "util/cocoa_globals.h"
#include "util/utility.h"
#include "util/statistics_registry.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace ff {

TheoryFiniteFields::TheoryFiniteFields(Env& env,
                                       OutputChannel& out,
                                       Valuation valuation)
    : Theory(THEORY_FF, env, out, valuation),
      d_state(env, valuation),
      d_im(env, *this, d_state, getStatsPrefix(THEORY_FF)),
      d_eqNotify(d_im),
      d_stats(std::make_unique<FfStatistics>(statisticsRegistry(), "theory::ff::"))
{
  d_theoryState = &d_state;
  d_inferManager = &d_im;
  // must be initialized before using CoCoA.
  initCocoaGlobalManager();
}

TheoryFiniteFields::~TheoryFiniteFields() {}

TheoryRewriter* TheoryFiniteFields::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryFiniteFields::getProofChecker() { return nullptr; }

bool TheoryFiniteFields::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_eqNotify;
  esi.d_name = "theory::ff::ee";
  // TODO: not needed, I think
  // esi.d_notifyNewClass = true;
  // esi.d_notifyMerge = true;
  // esi.d_notifyDisequal = true;
  return true;
}

void TheoryFiniteFields::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_MULT);
  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_NEG);
  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_ADD);
}

void TheoryFiniteFields::postCheck(Effort level)
{
  Trace("ff::check") << "ff::check : " << level << std::endl;
  for (auto& subTheory : d_subTheories)
  {
    subTheory.second.postCheck(level);
    if (subTheory.second.inConflict())
    {
      d_im.conflict(
          NodeManager::currentNM()->mkAnd(subTheory.second.conflict()),
          InferenceId::ARITH_FF);
    }
  }
}

void TheoryFiniteFields::notifyFact(TNode atom,
                                    bool polarity,
                                    TNode fact,
                                    bool isInternal)
{
  Trace("ff::check") << "ff::notifyFact : " << fact << " @ level "
                     << context()->getLevel() << std::endl;
  d_subTheories.at(atom[0].getType()).notifyFact(fact);
}

bool TheoryFiniteFields::collectModelValues(TheoryModel* m,
                                            const std::set<Node>& termSet)
{
  Trace("ff::model") << "Term set: " << termSet << std::endl;
  for (const auto& subTheory : d_subTheories)
  {
    for (const auto& entry : subTheory.second.model())
    {
      Trace("ff::model") << "Model entry: " << entry.first << " -> "
                         << entry.second << std::endl;
      if (termSet.count(entry.first))
      {
        bool okay = m->assertEquality(entry.first, entry.second, true);
        Assert(okay) << "Our model was rejected";
      }
    }
  }
  return true;
}

void TheoryFiniteFields::computeCareGraph()
{
  // TODO
}

TrustNode TheoryFiniteFields::explain(TNode node)
{
  // TODO
  return TrustNode::null();
}

Node TheoryFiniteFields::getModelValue(TNode node)
{
  // TODO
  return Node::null();
}

void TheoryFiniteFields::preRegisterTerm(TNode node)
{
  Trace("ff::preRegisterTerm") << "ff::preRegisterTerm : " << node << std::endl;
  TypeNode ty = node.getType();
  TypeNode fieldTy = ty;
  if (!ty.isFiniteField())
  {
    Assert(node.getKind() == Kind::EQUAL);
    fieldTy = node[0].getType();
  }
  if (d_subTheories.count(fieldTy) == 0)
  {
    d_subTheories.try_emplace(
        fieldTy, d_env, d_stats.get(), ty.getFiniteFieldSize());
  }
  d_subTheories.at(fieldTy).preRegisterTerm(node);
}

TrustNode TheoryFiniteFields::ppRewrite(TNode n, std::vector<SkolemLemma>& lems)
{
  // TODO
  return TrustNode::null();
}

Theory::PPAssertStatus TheoryFiniteFields::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  TNode in = tin.getNode();
  Trace("ff::pp") << "ff::ppAssert : " << in << std::endl;
  Theory::PPAssertStatus status = Theory::PP_ASSERT_STATUS_UNSOLVED;
  return status;
}

void TheoryFiniteFields::presolve()
{
  // TODO
}

bool TheoryFiniteFields::isEntailed(Node n, bool pol)
{
  // TODO
  return false;
}

CoCoA::RingElem bigPower(CoCoA::RingElem b, CoCoA::BigInt e)
{
  CoCoA::RingElem acc = CoCoA::one(CoCoA::owner(b));
  CoCoA::BigInt two = CoCoA::BigInt(2);
  while (!CoCoA::IsZero(e))
  {
    if (CoCoA::IsOdd(e))
    {
      acc *= b;
      e -= 1;
    }
    b *= b;
    CoCoA::divexact(e, e, two);
  }
  return acc;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
