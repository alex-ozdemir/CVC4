/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory of booleans.
 */

#include "theory/booleans/theory_bool.h"

#include <stack>
#include <vector>

#include "proof/proof_node_manager.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/booleans/theory_bool_rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory.h"
#include "theory/trust_substitutions.h"
#include "theory/valuation.h"
#include "util/hash.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace booleans {

TheoryBool::TheoryBool(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_BOOL, env, out, valuation),
      d_rewriter(nodeManager()),
      d_checker(nodeManager())
{
}

bool TheoryBool::ppAssert(TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  Assert(tin.getKind() == TrustNodeKind::LEMMA);
  TNode in = tin.getNode();
  if (in.getKind() == Kind::CONST_BOOLEAN)
  {
    if (in.getConst<bool>())
    {
      return true;
    }
    // should not be a false literal, which should be caught by preprocessing
    Assert(in.getConst<bool>());
  }

  // Add the substitution from the variable to its value
  if (in.getKind() == Kind::NOT)
  {
    if (in[0].isVar())
    {
      outSubstitutions.addSubstitutionSolved(
          in[0], nodeManager()->mkConst<bool>(false), tin);
      return true;
    }
    else if (in[0].getKind() == Kind::EQUAL && in[0][0].getType().isBoolean())
    {
      TNode eq = in[0];
      if (eq[0].isVar() && d_valuation.isLegalElimination(eq[0], eq[1]))
      {
        outSubstitutions.addSubstitutionSolved(eq[0], eq[1].notNode(), tin);
        return true;
      }
      else if (eq[1].isVar() && d_valuation.isLegalElimination(eq[1], eq[0]))
      {
        outSubstitutions.addSubstitutionSolved(eq[1], eq[0].notNode(), tin);
        return true;
      }
    }
  }
  else if (in.isVar())
  {
    outSubstitutions.addSubstitutionSolved(
        in, nodeManager()->mkConst<bool>(true), tin);
    return true;
  }

  // the positive Boolean equality case is handled in the default way
  return Theory::ppAssert(tin, outSubstitutions);
}

TheoryRewriter* TheoryBool::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryBool::getProofChecker() { return &d_checker; }

std::string TheoryBool::identify() const { return std::string("TheoryBool"); }

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5::internal
