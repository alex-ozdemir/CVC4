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
 * replace disjunctive bit constraints with polynomial bit constraints
 */

#include "preprocessing/passes/ff_disjunctive_bit.h"

// external includes

// std includes

// internal includes
#include "preprocessing/assertion_pipeline.h"
#include "theory/ff/parse.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

FfDisjunctiveBit::FfDisjunctiveBit(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ff-disjunctive-bit")
{
}

PreprocessingPassResult FfDisjunctiveBit::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  auto nm = NodeManager::currentNM();
  for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    Node fact = (*assertionsToPreprocess)[i];
    if (fact.getKind() == kind::OR && fact.getNumChildren() == 2
        && fact[0].getKind() == kind::EQUAL && fact[1].getKind() == kind::EQUAL
        && fact[0][1].getType().isFiniteField()
        && fact[1][0].getType().isFiniteField())
    {
      using theory::ff::parse::oneConstraint;
      using theory::ff::parse::zeroConstraint;
      if ((oneConstraint(fact[0]) && zeroConstraint(fact[1]))
          || (oneConstraint(fact[1]) && zeroConstraint(fact[0])))
      {
        using theory::ff::parse::spectrum;
        Node var = spectrum(fact[0])->var;
        Trace("ff::disjunctive-bit")
            << "rw bit constraint on: " << var << std::endl;
        Node var2 = nm->mkNode(kind::FINITE_FIELD_MULT, var, var);
        assertionsToPreprocess->replace(i, nm->mkNode(kind::EQUAL, var2, var));
      }
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
