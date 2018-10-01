/*********************                                                        */
/*! \file drat_bitvector_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector proof using the DRAT proof format
 **
 ** Contains DRAT-specific printing logic.
 **/

#include "cvc4_private.h"

#include <algorithm>
#include <iterator>
#include <set>
#include "options/bv_options.h"
#include "proof/clausal_bitvector_proof.h"
#include "proof/lfsc_proof_printer.h"
#include "proof/lrat/lfsc_lrat_printer.h"
#include "theory/bv/theory_bv.h"

namespace CVC4 {

namespace proof {

ClausalBitVectorProof::ClausalBitVectorProof(theory::bv::TheoryBV* bv,
                                             TheoryProofEngine* proofEngine)
    : BitVectorProof(bv, proofEngine), d_drat_proof(), d_lrat_proof()
{
}

ClausalBitVectorProof::~ClausalBitVectorProof()
{
  for (auto idAndClause = d_usedClauses.cbegin();
       idAndClause != d_usedClauses.cend();
       ++idAndClause)
  {
    delete idAndClause->second;
  }
};

void ClausalBitVectorProof::attachToSatSolver(prop::SatSolver& sat_solver)
{
  sat_solver.setClausalProofLog(this);
}

void ClausalBitVectorProof::initCnfProof(prop::CnfStream* cnfStream,
                                         context::Context* cnf,
                                         prop::SatVariable trueVar,
                                         prop::SatVariable falseVar)
{
  BitVectorProof::initCnfProof(cnfStream, cnf, trueVar, falseVar);
  prop::SatClause c;
  c.push_back(prop::SatLiteral(trueVar, false));
  registerUsedClause(d_cnfProof->getTrueUnitClause(), c);

  c[0] = prop::SatLiteral(falseVar, true);
  registerUsedClause(d_cnfProof->getFalseUnitClause(), c);
}

void ClausalBitVectorProof::registerUsedClause(ClauseId id,
                                               prop::SatClause& clause)
{
  prop::SatClause* clause_ptr = new prop::SatClause(clause);
  d_usedClauses.insert(std::make_pair(id, clause_ptr));
  d_satSolverInput.push_back(id);
};

const std::unordered_map<ClauseId, prop::SatClause*>&
ClausalBitVectorProof::getUsedClauses()
{
  return d_usedClauses;
}

void ClausalBitVectorProof::translate()
{
  d_lrat_proof.reset(
      new lrat::LRATProof(d_usedClauses, d_satSolverInput, d_drat_proof));
}

LFSCClausalBitVectorProof::LFSCClausalBitVectorProof(
    theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
    : ClausalBitVectorProof(bv, proofEngine)
{
}

std::string LFSCClausalBitVectorProof::printProofOfSatSolverInput(
    std::ostream& os, std::ostream& paren)
{
  if (Debug.isOn("pf::clausal"))
  {
    Debug("pf::clausal") << "Clauses: " << std::endl;
    for (auto cid = d_satSolverInput.cbegin(); cid != d_satSolverInput.cend();
         ++cid)
    {
      Debug("pf::clausal") << "  " << *(d_usedClauses[*cid]) << std::endl;
    }
  }
  std::vector<ClauseId> usedClauseIds;
  for (auto& p : d_usedClauses)
  {
    usedClauseIds.push_back(p.first);
  }
  std::string proofValueName("sat_input_proof");
  os << "(@ " << proofValueName << " ";
  paren << ')';
  lrat::LFSCLRATPrinter::printProofOfCMap(os, d_satSolverInput, d_usedClauses);
  os << '\n';
  return proofValueName;
}

std::string LFSCClausalBitVectorProof::printLRATProotLet(std::ostream& os,
                                                         std::ostream& paren)
{
  std::string proofValueName("lrat_proof");
  os << "(@ " << proofValueName << " ";
  paren << ')';
  lrat::LFSCLRATPrinter printer(*d_lrat_proof);
  printer.print(os);
  os << '\n';
  return proofValueName;
}

void LFSCClausalBitVectorProof::printTheoryLemmaProof(std::vector<Expr>& lemma,
                                                      std::ostream& os,
                                                      std::ostream& paren,
                                                      const ProofLetMap& map)
{
  Unimplemented();
}

void LFSCClausalBitVectorProof::printBBHelpers(std::ostream& os,
                                               std::ostream& paren,
                                               ProofLetMap& letMap)
{
  os << std::endl << ";; Bitblasting atom mappings" << std::endl;
  printBitblasting(os, paren);

  os << std::endl << ";; BB-CNF atom mappings" << std::endl;
  d_cnfProof->printAtomMapping(d_atomsInBitblastingProof, os, paren, letMap);

  os << std::endl << ";; BB-CNF proofs" << std::endl;
  for (IdToSatClause::iterator it = d_usedClauses.begin();
       it != d_usedClauses.end();
       ++it)
  {
    d_cnfProof->printCnfProofForClause(it->first, it->second, os, paren);
  }
}

void LFSCClausalBitVectorProof::printEmptyClauseProof(std::ostream& os,
                                                      std::ostream& paren)
{
  Assert(options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER,
         "the BV theory should only be proving bottom directly in the eager "
         "bitblasting mode");

  os << std::endl << ";; Proof of input to SAT solver" << std::endl;
  std::string satInputProofValueIdent = printProofOfSatSolverInput(os, paren);

  os << std::endl << ";; LRAT proof value" << std::endl;
  std::string lratProofIdent = printLRATProotLet(os, paren);

  os << std::endl << ";; Verification of LRAT Proof" << std::endl;
  os << "(lrat_proof_of_bottom _ " << satInputProofValueIdent << " "
     << lratProofIdent << ")" << std::endl;
}

void ClausalBitVectorProof::calculateAtomsInBitblastingProof()
{
  // Translate DRAT to LRAT
  translate();

  if (Debug.isOn("pf::clausal"))
  {
    size_t nClauses = d_usedClauses.size();
    std::set<prop::SatVariable> usedVars;
    for (const auto& c : d_usedClauses)
    {
      for (auto l : *(c.second))
      {
        usedVars.insert(l.getSatVariable());
      }
    }
    size_t nVariables = usedVars.size();

    Debug("pf::clausal") << "A DIMACS problem follows:" << std::endl;
    Debug("pf::clausal") << "p cnf " << nVariables << " " << nClauses
                         << std::endl;
    for (const auto& c : d_usedClauses)
    {
      for (auto l : *(c.second))
      {
        if (l.isNegated())
        {
          Debug("pf::clausal") << "-" << l.getSatVariable() + 1 << " ";
        }
        else
        {
          Debug("pf::clausal") << l.getSatVariable() + 1 << " ";
        }
      }
      Debug("pf::clausal") << '0' << std::endl;
    }
  }
  d_cnfProof->collectAtomsForClauses(d_usedClauses, d_atomsInBitblastingProof);
}

}  // namespace proof

};  // namespace CVC4
