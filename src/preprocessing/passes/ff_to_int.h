/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The ff-to-int preprocessing pass.
 */

#ifndef __CVC5__PREPROCESSING__PASSES__FF_TO_INT_H
#define __CVC5__PREPROCESSING__PASSES__FF_TO_INT_H

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "context/context.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/ff/to_int.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class FfToInt : public PreprocessingPass
{
 public:
  FfToInt(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

  // Add the lemmas in `additionalConstraints` to the assertions pipeline.
  void addFinalizeAssertions(AssertionPipeline* assertionsToPreprocess,
                             const std::vector<Node>& additionalConstraints);

  // include the skolem map as substitutions
  void addSkolemDefinitions(const std::map<Node, Node>& skolems);

 private:
  /** conversions from field elements to integers */
  theory::ff::ToInt d_toInt;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* __CVC5__PREPROCESSING__PASSES__FF_TO_INT_H */
