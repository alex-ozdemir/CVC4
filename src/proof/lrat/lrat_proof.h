/*********************                                                        */
/*! \file lrat_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief LRAT Proof Format
 **
 ** Declares C++ types that represent a LRAT proof.
 ** Defines serialization for these types.
 ** Follows: https://www.cs.utexas.edu/~marijn/publications/lrat.pdf
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__LRATPROOF_H
#define __CVC4__PROOF__LRATPROOF_H 0

#include <vector>
#include <unordered_map>

#include "base/output.h"
#include "proof/clause_id.h"
#include "proof/drat/drat_proof.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {
namespace proof {
namespace lrat {

// Refers to clause position within an LRAT proof
using ClauseIdx = size_t;

enum LRATInstructionKind
{
  lratDeletion,
  lratAddition,
};

struct LRATDeletionData
{
  // This idx doesn't really matter, but it's in the format anyway, so we parse
  // it.
  ClauseIdx idxOfClause;

  // Clauses to delete
  std::vector<ClauseIdx> clauses;
};

// A sequence of locations that will contain unit clauses during unit
// propegation
using LRATUPTrace = std::vector<ClauseIdx>;

struct LRATAdditionData
{
  // The idx for the new clause
  ClauseIdx idxOfClause;
  // The new clause
  prop::SatClause clause;
  // UP trace based on the negation of that clause
  LRATUPTrace atTrace;

  // Clauses that can resolve with `clause` on its first variable,
  // together with a UP trace after that resolution.
  // Used for RAT checks.
  std::vector<std::pair<ClauseIdx, LRATUPTrace>> resolvants;
};

union LRATInstructionData
{
  LRATDeletionData deletion;
  LRATAdditionData addition;
};

// This is conceptually a Either<Addition,Deletion>
struct LRATInstruction
{
  LRATInstructionKind kind;
  LRATAdditionData additionData;
  LRATDeletionData deletionData;
};

class LRATProof
{
 public:
  LRATProof(const std::unordered_map<ClauseId, prop::SatClause*>& usedClauses,
            const std::vector<ClauseId>& clauseOrder,
            const drat::DRATProof& drat);
  LRATProof(std::istream& textualProof);

  inline const std::vector<LRATInstruction>& getInstructions() const
  {
    return d_instructions;
  }

 private:
  std::vector<LRATInstruction> d_instructions;
};

// Prints the literal as a (+) or (-) int
inline std::ostream& textOut(std::ostream& o, const prop::SatLiteral& l)
{
  if (l.isNegated())
  {
    o << "-";
  }
  return o << l.getSatVariable();
}

// Prints the clause as a space-separated list of ints
inline std::ostream& textOut(std::ostream& o, const prop::SatClause& c)
{
  for (const auto l : c)
  {
    textOut(o, l) << " ";
  }
  return o << "0";
}

// Prints the trace as a space-separated list of (+) ints with a space at the
// end.
inline std::ostream& operator<<(std::ostream& o, const LRATUPTrace& trace)
{
  for (const auto i : trace)
  {
    o << i << " ";
  }
  return o;
}

// Prints the LRAT addition line in textual format
inline std::ostream& operator<<(std::ostream& o, const LRATAdditionData& add)
{
  o << add.idxOfClause << " ";
  textOut(o, add.clause) << " ";
  o << add.atTrace;  // Inludes a space at the end.
  for (const auto& rat : add.resolvants)
  {
    o << "-" << rat.first << " ";
    o << rat.second;  // Includes a space at the end.
  }
  o << "0\n";
  return o;
}

// Prints the LRAT addition line in textual format
inline std::ostream& operator<<(std::ostream& o, const LRATDeletionData& del)
{
  o << del.idxOfClause << " d ";
  for (const auto& idx : del.clauses)
  {
    o << idx << " ";
  }
  return o << "0\n";
}

// Prints the LRAT line in textual format
inline std::ostream& operator<<(std::ostream& o, const LRATInstruction& i)
{
  switch (i.kind)
  {
    case lratAddition: return o << i.additionData;
    case lratDeletion: return o << i.deletionData;
    default: return o;
  }
}

// Prints the LRAT proof in textual format
inline std::ostream& operator<<(std::ostream& o, const LRATProof& p)
{
  for (const auto& instr : p.getInstructions())
  {
    o << instr;
  }
  return o;
}

}  // namespace lrat
}  // namespace proof
}  // namespace CVC4

#endif
