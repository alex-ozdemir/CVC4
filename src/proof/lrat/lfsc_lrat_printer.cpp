/*********************                                                        */
/*! \file lfsc_lrat_printer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief LFSC LRAT printing machinery
 **/

#include "proof/lrat/lfsc_lrat_printer.h"
#include <iostream>
#include "proof/lfsc_proof_printer.h"

namespace CVC4 {
namespace proof {
namespace lrat {

LFSCLRATPrinter::LFSCLRATPrinter(const LRATProof& proof) : d_proof(proof)
{
  // Nothing else
}

void LFSCLRATPrinter::print(std::ostream& o)
{
  const std::vector<LRATInstruction>& instructions = d_proof.getInstructions();
  for (const LRATInstruction& i : instructions)
  {
    switch (i.kind)
    {
      case lratAddition:
      {
        o << "\n    (LRATProofa " << i.additionData.idxOfClause << " ";
        LFSCProofPrinter::printSatClause(i.additionData.clause, o, "bb");
        o << " ";
        printTrace(o, i.additionData.atTrace);
        o << " ";
        printHints(o, i.additionData.resolvants);
        o << " ";
        break;
      }
      case lratDeletion:
      {
        o << "\n    (LRATProofd ";
        printIndices(o, i.deletionData.clauses);
        o << " ";
        break;
      }
    }
  }
  o << "LRATProofn";
  std::fill_n(std::ostream_iterator<char>(o), instructions.size(), ')');
}

void LFSCLRATPrinter::printTrace(std::ostream& o, const LRATUPTrace& trace)
{
  for (ClauseIdx idx : trace)
  {
    o << "(Tracec " << idx << " ";
  }
  o << "Tracen";
  std::fill_n(std::ostream_iterator<char>(o), trace.size(), ')');
}

void LFSCLRATPrinter::printProofOfCMap(
    std::ostream& o,
    const std::vector<ClauseId>& cnf,
    const std::unordered_map<ClauseId, prop::SatClause*>& cs)
{
  for (size_t i = 0; i < cnf.size(); ++i)
  {
    o << "\n    (CMapc_proof " << (i + 1) << " _ _ ";
    o << ProofManager::getInputClauseName(cnf[i], "bb") << " ";
    o << " ";
  }
  o << "CMapn_proof";
  std::fill_n(std::ostream_iterator<char>(o), cnf.size(), ')');
}

void LFSCLRATPrinter::printCMap(std::ostream& o,
                                const std::vector<prop::SatClause>& cnf)
{
  for (size_t i = 0; i < cnf.size(); ++i)
  {
    o << "\n    (CMapc " << (i + 1) << " ";
    LFSCProofPrinter::printSatClause(cnf[i], o, "bb");
    o << " ";
  }
  o << "CMapn";
  std::fill_n(std::ostream_iterator<char>(o), cnf.size(), ')');
}

void LFSCLRATPrinter::printHints(
    std::ostream& o,
    const std::vector<std::pair<ClauseIdx, LRATUPTrace>>& hints)
{
  for (auto& hint : hints)
  {
    o << "\n    (RATHintsc " << hint.first << " ";
    printTrace(o, hint.second);
    o << " ";
  }
  o << "RATHintsn";
  std::fill_n(std::ostream_iterator<char>(o), hints.size(), ')');
}

void LFSCLRATPrinter::printIndices(std::ostream& o,
                                   const std::vector<ClauseIdx>& indices)
{
  for (ClauseIdx idx : indices)
  {
    o << "(CIListc " << idx << " ";
  }
  o << "CIListn";
  std::fill_n(std::ostream_iterator<char>(o), indices.size(), ')');
}

}  // namespace lrat
}  // namespace proof
}  // namespace CVC4
