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
 * The FfToInt preprocessing pass.
 *
 * Converts finite-field operations into integer operations.
 *
 */

#include "preprocessing/passes/ff_to_int.h"

#include <cmath>
#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;
using namespace cvc5::internal::theory::ff;

FfToInt::FfToInt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ff-to-int"),
      d_toInt(preprocContext->getEnv())
{
}

PreprocessingPassResult FfToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // vector of boolean nodes for additional constraints
  // this will always contain range constraints
  // and for options::SolveBVAsIntMode::BITWISE, it will
  // also include bitwise assertion constraints
  std::vector<Node> additionalConstraints;
  std::map<Node, Node> skolems;
  for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    Node ffNode = (*assertionsToPreprocess)[i];
    Node intNode = d_toInt.toInt(ffNode, additionalConstraints, skolems);
    Node rwNode = rewrite(intNode);
    Trace("ff::to-int") << "ff node: " << ffNode << std::endl;
    Trace("ff::to-int") << "int node: " << intNode << std::endl;
    Trace("ff::to-int") << "rw node: " << rwNode << std::endl;
    assertionsToPreprocess->replace(i, rwNode);
  }
  addFinalizeAssertions(assertionsToPreprocess, additionalConstraints);
  addSkolemDefinitions(skolems);
  return PreprocessingPassResult::NO_CONFLICT;
}

void FfToInt::addSkolemDefinitions(const std::map<Node, Node>& skolems)
{
  for (const auto& it : skolems)
  {
    Node originalSkolem = it.first;
    Node definition = it.second;
    std::vector<Node> args;
    Node body;
    if (definition.getType().isFunction())
    {
      Unimplemented();
    }
    else
    {
      body = definition;
    }
    Trace("ff::to-int") << "adding substitution: "
                        << "[" << originalSkolem << "] ----> [" << definition
                        << "]" << std::endl;
    d_preprocContext->addSubstitution(originalSkolem, definition);
  }
}

void FfToInt::addFinalizeAssertions(
    AssertionPipeline* assertionsToPreprocess,
    const std::vector<Node>& additionalConstraints)
{
  NodeManager* nm = NodeManager::currentNM();
  Node lemmas = nm->mkAnd(additionalConstraints);
  assertionsToPreprocess->push_back(lemmas);
  Trace("ff::to-int") << "side assertion: " << lemmas.toString() << std::endl;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
