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

#include <numeric>
#include <unordered_map>

#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"
#include "expr/node_manager_attributes.h"
#include "expr/node_traversal.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace ff {

TheoryFiniteFields::TheoryFiniteFields(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_FF, env, out, valuation),
      d_state(env, valuation),
      d_im(env, *this, d_state, getStatsPrefix(THEORY_FF)),
      d_eqNotify(d_im),
      d_ffFacts(context()),
      d_cocoaGlobalManager()
{
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryFiniteFields::~TheoryFiniteFields()
{
}

TheoryRewriter* TheoryFiniteFields::getTheoryRewriter()
{
  return &d_rewriter;
}

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
  // Handle ff facts
  if (!d_ffFacts.empty() && Theory::fullEffort(level))
  {
    if (!isSat(d_ffFacts))
    {
      std::vector<Node> conflict(d_ffFacts.begin(), d_ffFacts.end());
      d_im.conflict(NodeManager::currentNM()->mkAnd(conflict), InferenceId::ARITH_FF);
    }
  }
}

void TheoryFiniteFields::notifyFact(TNode atom,
                            bool polarity,
                            TNode fact,
                            bool isInternal)
{
  Trace("ff::check") << "ff::notifyFact : " << atom << " = " << polarity << std::endl;
  if (polarity)
  {
    d_ffFacts.push_back(atom);
  }
  else
  {
    d_ffFacts.push_back(atom.notNode());
  }
}

bool TheoryFiniteFields::collectModelValues(TheoryModel* m,
                                    const std::set<Node>& termSet)
{
  // TODO
  return false;
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
  // TODO
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

bool TheoryFiniteFields::isEntailed( Node n, bool pol )
{
  // TODO
  return false;
}

bool isSat(const context::CDList<Node>& assertions)
{
  std::unordered_set<Node> vars = getVars(assertions);
  std::unordered_set<Integer, IntegerHashFunction> sizes =
      getFieldSizes(assertions);
  if (TraceIsOn("ff::check"))
  {
    Trace("ff::check") << "Vars: " << std::endl;
    for (const auto& v : vars)
    {
      Trace("ff::check") << " - " << v << std::endl;
    }
    Trace("ff::check") << "Sizes: " << std::endl;
    for (const auto& v : sizes)
    {
      Trace("ff::check") << " - " << v << std::endl;
    }
  }
  AlwaysAssert(sizes.size() == 1)
      << "Unsupported: multiple field sizes. See ff::check channel.";
  CoCoA::BigInt size = CoCoA::BigIntFromString(sizes.begin()->toString());
  CoCoA::QuotientRing ringFp = CoCoA::NewZZmod(size);
  std::vector<Node> nodes;
  std::vector<CoCoA::symbol> symbolVec;
  std::vector<CoCoA::symbol> invSyms;
  for (const auto& var : vars)
  {
    CoCoA::symbol sym(var.getAttribute(expr::VarNameAttr()));
    symbolVec.push_back(sym);
    nodes.push_back(var);
  }
  size_t numDisequalities = countDisequalities(assertions);
  for (size_t i = 0; i < numDisequalities; ++i)
  {
    CoCoA::symbol sym("inv_witness", i);
    symbolVec.push_back(sym);
    invSyms.push_back(sym);
  }
  CoCoA::SparsePolyRing ringPoly = CoCoA::NewPolyRing(ringFp, symbolVec);
  std::unordered_map<Node, CoCoA::RingElem> varPolys;
  for (size_t i = 0; i < nodes.size(); ++i)
  {
    CoCoA::RingElem poly = CoCoA::indet(ringPoly, i);
    varPolys.insert(std::make_pair(nodes[i], poly));
  }
  std::unordered_map<Node, CoCoA::RingElem> nodePolys(varPolys);
  std::vector<CoCoA::RingElem> invPolys;
  for (size_t i = 0; i < numDisequalities; ++i)
  {
    invPolys.push_back(CoCoA::indet(ringPoly, nodePolys.size() + i));
  }
  for (const auto& term : assertions)
  {
    for (const auto& node :
         NodeDfsIterable(term, VisitOrder::POSTORDER, [&nodePolys](TNode nn) {
           return nodePolys.count(nn) > 0;
         }))
    {
      if (node.getType().isFiniteField())
      {
        CoCoA::RingElem poly;
        std::vector<CoCoA::RingElem> subPolys;
        std::transform(node.begin(),
                       node.end(),
                       std::back_inserter(subPolys),
                       [&nodePolys](Node n) { return nodePolys[n]; });
        switch (node.getKind())
        {
          case Kind::FINITE_FIELD_ADD:
            poly = std::accumulate(
                subPolys.begin(),
                subPolys.end(),
                CoCoA::RingElem(ringPoly->myZero()),
                [](CoCoA::RingElem a, CoCoA::RingElem b) { return a + b; });
            break;
          case Kind::FINITE_FIELD_NEG: poly = -subPolys[0]; break;
          case Kind::FINITE_FIELD_MULT:
            poly = std::accumulate(
                subPolys.begin(),
                subPolys.end(),
                CoCoA::RingElem(ringPoly->myOne()),
                [](CoCoA::RingElem a, CoCoA::RingElem b) { return a * b; });
            break;
          case Kind::CONST_FINITE_FIELD:
          {
            CoCoA::BigInt constant = CoCoA::BigIntFromString(
                node.getConst<FiniteField>().getValue().toString());
            poly = ringPoly->myOne() * constant;
            break;
          }
          default:
            Unreachable() << "Invalid finite field kind: " << node.getKind();
        }
        Trace("ff::check") << "Translated " << node << "\t-> " << poly
                           << std::endl;
        nodePolys.insert(std::make_pair(node, poly));
      }
    }
  }
  std::vector<CoCoA::RingElem> generators;
  size_t disequalityIndex = 0;
  for (const auto& assertion : assertions)
  {
    Trace("ff::check") << "Assertion " << assertion << std::endl;

    CoCoA::RingElem p = ringPoly->myZero();
    switch (assertion.getKind())
    {
      case Kind::EQUAL:
      {
        p = nodePolys[assertion[0]] - nodePolys[assertion[1]];
        Trace("ff::check") << "Translated " << assertion << "\t-> " << p
                           << std::endl;
        break;
      }
      case Kind::NOT:
      {
        AlwaysAssert(assertion[0].getKind() == Kind::EQUAL);
        Assert(disequalityIndex < numDisequalities);
        CoCoA::RingElem diff =
            nodePolys[assertion[0][0]] - nodePolys[assertion[0][1]];
        p = diff * invPolys[disequalityIndex] - ringPoly->myOne();
        ++disequalityIndex;
        break;
      }
      default:
        Unhandled() << "Kind " << assertion.getKind()
                    << " in finite field sat check";
    }
    Trace("ff::check") << "Translated " << assertion << "\t-> " << p
                       << std::endl;
    generators.push_back(p);
  }
  CoCoA::ideal ideal = CoCoA::ideal(generators);
  const auto basis = CoCoA::GBasis(ideal);
  Trace("ff::check") << "Groebner basis " << basis << std::endl;
  for (const auto& basisPoly : basis)
  {
    if (CoCoA::deg(basisPoly) == 0)
    {
      return false;
    }
  }

  return true;
}

std::unordered_set<Node> getVars(const context::CDList<Node>& terms)
{
  std::unordered_set<Node> vars;
  for (const auto& term : terms)
  {
    for (const auto& node : NodeDfsIterable(term))
    {
      if (node.isVar())
      {
        vars.insert(node);
      }
    }
  }
  return vars;
}

std::unordered_set<Integer, IntegerHashFunction> getFieldSizes(
    const context::CDList<Node>& terms)
{
  std::unordered_set<Integer, IntegerHashFunction> sizes = {};
  for (const auto& term : terms)
  {
    for (const auto& node : NodeDfsIterable(term))
    {
      TypeNode ty = node.getType();
      if (ty.isFiniteField())
      {
        sizes.insert(ty.getFiniteFieldSize());
      }
    }
  }
  return sizes;
}

size_t countDisequalities(const context::CDList<Node>& terms)
{
  size_t ct = 0;
  for (const auto& term : terms)
  {
    if (term.getKind() == Kind::NOT)
    {
      ++ct;
    }
  }
  return ct;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
