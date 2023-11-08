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
 * cocoa utilities
 */

#include "cvc5_private.h"

#ifdef CVC5_USE_COCOA

#ifndef CVC5__THEORY__FF__COCOA_H
#define CVC5__THEORY__FF__COCOA_H

// external includes
#include <CoCoA/ring.H>
#include <CoCoA/symbol.H>

// std includes
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>

// internal includes
#include "expr/node.h"
#include "theory/ff/util.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/** Create cocoa symbol, sanitizing varName. */
CoCoA::symbol cocoaSym(const std::string& varName,
                       std::optional<size_t> index = {});

class CocoaEncoder : public FieldObj
{
  enum class Stage
  {
    /** collecting: variable, !=, bitsum */
    Scan,
    /** encoding terms */
    Encode,
  };

 public:
  CocoaEncoder(const FfSize& size);
  CoCoA::symbol freshSym(const std::string& varName,
                         std::optional<size_t> index = {});
  void endScan();
  void addFact(const Node& fact);
  const std::vector<CoCoA::RingElem>& polys() const { return d_polys; }
  const std::vector<CoCoA::RingElem>& bitsumPolys() const
  {
    return d_bitsumPolys;
  }
  const CoCoA::RingElem& getTermEncoding(const Node& t) const
  {
    return d_cache.at(t);
  }
  std::vector<Node> bitsums() const;
  const CoCoA::ring& polyRing() const { return d_polyRing.value(); }
  std::vector<std::pair<size_t, Node>> nodeIndets() const;
  FiniteFieldValue cocoaFfToFfVal(const CoCoA::RingElem& elem);

 private:
  /** a bitsum or a var */
  const Node& symNode(CoCoA::symbol s) const;
  bool hasNode(CoCoA::symbol s) const;
  const CoCoA::RingElem& symPoly(CoCoA::symbol s) const;
  void encodeTerm(const Node& t);
  void encodeFact(const Node& f);

  // configuration
  CoCoA::ring d_coeffField;

  // populated during Stage::Scan

  Stage d_stage{Stage::Scan};
  std::unordered_set<Node> d_scanned{};
  std::unordered_set<std::string> d_vars{};
  std::unordered_map<Node, CoCoA::symbol> d_bitsumSyms{};
  std::unordered_map<Node, CoCoA::symbol> d_varSyms{};
  std::unordered_map<Node, CoCoA::symbol> d_diseqSyms{};
  std::unordered_map<std::string, Node> d_symNodes{};
  std::unordered_map<std::string, CoCoA::RingElem> d_symPolys{};
  std::vector<CoCoA::symbol> d_syms{};

  std::optional<CoCoA::ring> d_polyRing{};

  /** encoding cache */
  std::unordered_map<Node, CoCoA::RingElem> d_cache{};
  std::vector<CoCoA::RingElem> d_polys{};
  std::vector<CoCoA::RingElem> d_bitsumPolys{};
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__COCOA_H */

#endif /* CVC5_USE_COCOA */
