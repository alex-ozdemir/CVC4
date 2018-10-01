/*********************                                                        */
/*! \file lfsc_lrat_printer.h
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

#include "cvc4_private.h"

#ifndef __CVC4__PROOF__LFSC_LRAT_PRINTER_H
#define __CVC4__PROOF__LFSC_LRAT_PRINTER_H

#include <iosfwd>
#include <unordered_map>

#include "proof/lrat/lrat_proof.h"

namespace CVC4 {
namespace proof {
namespace lrat {

class LFSCLRATPrinter
{
 public:
  LFSCLRATPrinter(const LRATProof& proof);

  /**
   * Prints the LFSC LRAT proof structure
   */
  void print(std::ostream& o);

  /**
   * Print a proof of a cmap containing the given clauses
   */
  static void printProofOfCMap(
      std::ostream& o,
      const std::vector<ClauseId>& ids,
      const std::unordered_map<ClauseId, prop::SatClause*>& cs);

 private:
  /**
   * Print a list of clause indices to go to while doing UP.
   */
  static void printTrace(std::ostream& o, const LRATUPTrace& trace);

  /**
   * Print a map of clauses, indexed starting at 1.
   */
  static void printCMap(std::ostream& o,
                        const std::vector<prop::SatClause>& ids);

  /**
   * Print a clause
   */
  static void printHints(
      std::ostream& o,
      const std::vector<std::pair<ClauseIdx, LRATUPTrace>>& hints);

  /**
   * Print an index list
   */
  static void printIndices(std::ostream& o,
                           const std::vector<ClauseIdx>& indices);

  const LRATProof& d_proof;
};

}  // namespace lrat
}  // namespace proof
}  // namespace CVC4

#endif
