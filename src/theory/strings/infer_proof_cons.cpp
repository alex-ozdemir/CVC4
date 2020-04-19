/*********************                                                        */
/*! \file infer_proof_cons.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference to proof conversion
 **/

#include "theory/strings/infer_proof_cons.h"

#include "theory/strings/theory_strings_utils.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {

InferProofCons::InferProofCons(eq::ProofEqEngine& pfee) : d_pfee(pfee) {}

PfRule InferProofCons::convert(Node eq,
                               Inference infer,
                               const std::vector<Node>& exp,
                               const std::vector<Node>& expn,
                               std::vector<Node>& pfChildren,
                               std::vector<Node>& pfArgs)
{
  // TODO
  pfChildren.insert(pfChildren.end(), exp.begin(), exp.end());
  pfChildren.insert(pfChildren.end(), expn.begin(), expn.end());
  return PfRule::UNKNOWN;
}

PfRule InferProofCons::convert(Node eq,
                Inference infer,
                Node expConj,
                std::vector<Node>& pfChildren,
                std::vector<Node>& pfArgs)
{
  std::vector<Node> exp;
  utils::flattenOp(AND, expConj, exp);
  // no new literals
  std::vector<Node> expn;
  return convert(eq, infer, exp, expn, pfChildren, pfArgs);
}
  
}  // namespace strings
}  // namespace theory
}  // namespace CVC4