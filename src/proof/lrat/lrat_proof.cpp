/*********************                                                        */
/*! \file lrat_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief DRAT Proof Format
 **
 ** Defines deserialization for DRAT proofs.
 **/

#include "proof/lrat/lrat_proof.h"

#include "base/output.h"
#include "base/cvc4_assert.h"

#include "base/configuration_private.h"
#if (IS_DRATTRIM_BUILD && IS_PROOFS_BUILD)
// #include "drat-trim.h"
extern "C" int run_drat_trim(int, char**);
#endif

#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <fstream>
#include <unordered_map>

namespace CVC4 {
namespace proof {
namespace lrat {

using prop::SatClause;
using prop::SatLiteral;
using prop::SatVariable;

LRATProof::LRATProof(
    const std::unordered_map<ClauseId, prop::SatClause*>& usedClauses,
    const std::vector<ClauseId>& clauseOrder,
    const drat::DRATProof& drat)
{
#if (IS_DRATTRIM_BUILD && IS_PROOFS_BUILD)
  std::ostringstream cmd;
  char formulaFilename[] = "/tmp/cvc4-dimacs-XXXXXX";
  char dratFilename[] = "/tmp/cvc4-drat-XXXXXX";
  char lratFilename[] = "/tmp/cvc4-lrat-XXXXXX";
  int r;
  r = mkstemp(formulaFilename);
  Assert(r > 0);
  r = mkstemp(dratFilename);
  Assert(r > 0);
  r = mkstemp(lratFilename);
  Assert(r > 0);
  std::ofstream formStream(formulaFilename);
  size_t maxVar = 0;
  for (auto& c : usedClauses)
  {
    for (auto l : *(c.second))
    {
      if (l.getSatVariable() + 1 > maxVar)
      {
        maxVar = l.getSatVariable() + 1;
      }
    }
  }
  formStream << "p cnf " << maxVar << " " << usedClauses.size() << '\n';
  for (auto ci : clauseOrder)
  {
    auto iterator = usedClauses.find(ci);
    Assert(iterator != usedClauses.end());
    for (auto l : *(iterator->second))
    {
      if (l.isNegated())
      {
        formStream << '-';
      }
      formStream << l.getSatVariable() + 1 << " ";
    }
    formStream << "0\n";
  }
  formStream.close();

  std::ofstream dratStream(dratFilename);
  for (auto& i : drat.getInstructions())
  {
    if (i.kind == drat::deletion)
    {
      dratStream << "d ";
    }
    for (auto l : i.clause)
    {
      if (l.isNegated())
      {
        dratStream << '-';
      }
      dratStream << l.getSatVariable() + 1 << " ";
    }
    dratStream << "0\n";
  }
  dratStream.close();

  char * arguments[6];
  char libraryBinary[] = "??";
  char quietFlag[] = "-q";
  char lratFlag[] = "-L";
  arguments[0] = libraryBinary;
  arguments[1] = quietFlag;
  arguments[2] = formulaFilename;
  arguments[3] = dratFilename;
  arguments[4] = lratFlag;
  arguments[5] = lratFilename;
  int nArgs = 6;
  run_drat_trim(nArgs, arguments);


  cmd << "/home/aozdemir/repos/drat-trim/drat-trim ";
  cmd << formulaFilename << " ";
  cmd << dratFilename << " ";
  cmd << "-L " << lratFilename;
  cmd << " > /dev/null 2>&1";

  Debug("pf::lrat") << "Invoking:\n    " << cmd.str() << std::endl;
  int status = system(cmd.str().c_str());
  Assert(status == 0, "drat-trim invocation failed");
  std::ifstream lratStream(lratFilename);
  LRATProof lratProof(lratStream);
  remove(formulaFilename);
  remove(dratFilename);
  remove(lratFilename);
  *this = std::move(lratProof);
#else
  Unreachable(
      "This version of CVC4 was built without drat-trim;"
      "cannot produce eager BV proofs.");
#endif
}

std::istream& operator>>(std::istream& in, prop::SatLiteral& l)
{
  long int i;
  in >> i;
  l = prop::SatLiteral(labs(i), i < 0);
  return in;
}

// This parser is implemented to parse the textual RAT format found in
// "Efficient Certified RAT Verification", by Cruz-Filipe et. All
LRATProof::LRATProof(std::istream& textualProof)
{
  for (size_t line = 0;; ++line)
  {
    LRATInstruction instr;

    // Read beginning of instruction. EOF indicates that we're done.
    size_t clauseIdx;
    textualProof >> clauseIdx;
    if (textualProof.eof())
    {
      return;
    }

    // Read the first word of the instruction. A 'd' indicates deletion.
    std::string first;
    textualProof >> first;
    Trace("pf::lrat") << "First word: " << first << std::endl;
    Assert(textualProof.good());
    if (first == "d")
    {
      instr.kind = lratDeletion;
      instr.deletionData.idxOfClause = clauseIdx;
      while (true)
      {
        ClauseIdx di;
        textualProof >> di;
        Assert(textualProof.good());
        if (di == 0)
        {
          break;
        }
        instr.deletionData.clauses.push_back(di);
      }
      std::sort(instr.deletionData.clauses.begin(),
                instr.deletionData.clauses.end());
    }
    else
    {
      instr.kind = lratAddition;
      instr.additionData.idxOfClause = clauseIdx;

      // We need to reparse the first word as a literal to read the clause
      // we're parsing. It ends with a 0;
      std::istringstream firstS(first);
      SatLiteral lit;
      firstS >> lit;
      Trace("pf::lrat") << "First lit: " << lit << std::endl;
      Assert(!firstS.fail(), "Couldn't parse first literal from addition line");
      for (; lit != 0; textualProof >> lit)
      {
        Assert(textualProof.good());
        SatLiteral l(lit.getSatVariable() - 1, lit.isNegated());
        instr.additionData.clause.push_back(l);
      }

      // Now we read the AT UP trace. It ends at the first non-(+) #
      long int i;
      textualProof >> i;
      for (; i > 0; textualProof >> i)
      {
        Assert(textualProof.good());
        instr.additionData.atTrace.push_back(i);
      }

      // For each RAT hint... (each RAT hint starts with a (-).
      for (; i<0; textualProof>> i)
      {
        Assert(textualProof.good());
        // Create an entry in the RAT hint list
        instr.additionData.resolvants.push_back(
            make_pair(-i, std::vector<ClauseIdx>()));

        // Record the UP trace. It ends with a (-) or 0.
        textualProof >> i;
        for (; i > 0; textualProof >> i)
        {
          instr.additionData.resolvants.back().second.push_back(i);
        }
      }
      // Pairs compare based on the first element, so this sorts by the
      // resolution target index
      std::sort(instr.additionData.resolvants.begin(),
                instr.additionData.resolvants.end());
    }
    Debug("pf::lrat") << "Instr: " << instr << std::endl;
    d_instructions.push_back(instr);
  }
}

}  // namespace lrat
}  // namespace proof
}  // namespace CVC4
