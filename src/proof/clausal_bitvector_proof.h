/*********************                                                        */
/*! \file clausal_bitvector_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector proof using the DRAT & LRAT proof formats
 **
 ** An internal string stream is hooked up to cryptominisat, which spits out a
 ** binary DRAT proof. That proof is decoded, re-encoded textually, and then
 ** fed into drat-trim, which spits out an LRAT proof. That proof is printed
 ** in LFSC.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__CLAUSAL_BITVECTOR_PROOF_H
#define __CVC4__PROOF__CLAUSAL_BITVECTOR_PROOF_H

#include <iostream>
#include <sstream>
#include <unordered_map>

#include "expr/expr.h"
#include "proof/bitvector_proof.h"
#include "proof/lrat/lrat_proof.h"
#include "proof/theory_proof.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver_types.h"
#include "theory/bv/bitblast/bitblaster.h"
#include "theory/bv/theory_bv.h"

namespace CVC4 {

namespace proof {

class ClausalBitVectorProof : public BitVectorProof
{
 public:
  ClausalBitVectorProof(theory::bv::TheoryBV* bv,
                        TheoryProofEngine* proofEngine);

  virtual ~ClausalBitVectorProof();

  void attachToSatSolver(prop::SatSolver& sat_solver) override;

  void initCnfProof(prop::CnfStream* cnfStream,
                    context::Context* cnf,
                    prop::SatVariable trueVar,
                    prop::SatVariable falseVar) override;

  void registerUsedClause(ClauseId id, prop::SatClause& clause);

  void calculateAtomsInBitblastingProof() override;

  const std::unordered_map<ClauseId, prop::SatClause*>& getUsedClauses();

  inline std::ostream& getDRATOstream()
  {
    return d_drat_proof.getOStringStream();
  }

 protected:
  void translate();

  // The SatClauses therein are owned by this data structure.
  std::unordered_map<ClauseId, prop::SatClause*> d_usedClauses;
  // The clauses that were given to the sat solver, in order
  std::vector<ClauseId> d_satSolverInput;

  // Recieved from cryptominisat
  drat::DRATProof d_drat_proof;

  // Really, this should just be std::optional
  std::unique_ptr<lrat::LRATProof> d_lrat_proof;
};

class LFSCClausalBitVectorProof : public ClausalBitVectorProof
{
  /**
   * The SAT solver is given a list of clauses.
   * Assuming that each clause has alreay been individually proven,
   * defines a proof of the input to the SAT solver.
   *
   * Returns the name of the proof.
   */
  std::string printProofOfSatSolverInput(std::ostream& os, std::ostream& paren);

  std::string printLRATProotLet(std::ostream& os, std::ostream& paren);

 public:
  LFSCClausalBitVectorProof(theory::bv::TheoryBV* bv,
                            TheoryProofEngine* proofEngine);

  void printTheoryLemmaProof(std::vector<Expr>& lemma,
                             std::ostream& os,
                             std::ostream& paren,
                             const ProofLetMap& map) override;
  void printBBHelpers(std::ostream& os,
                      std::ostream& paren,
                      ProofLetMap& letMap) override;
  void printEmptyClauseProof(std::ostream& os, std::ostream& paren) override;
};

}  // namespace proof

}  // namespace CVC4

#endif /* __CVC4__PROOF__CLAUSAL_BITVECTOR_PROOF_H */
