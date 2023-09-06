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
 * a split groebner basis
 */

#ifdef CVC5_USE_COCOA

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__SPLIT_GB_H
#define CVC5__THEORY__FF__SPLIT_GB_H

// external includes
#include <CoCoA/ring.H>
#include <CoCoA/symbol.H>

// std includes
#include <memory>
#include <optional>
#include <vector>

// internal includes
#include "theory/ff/igb.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

class SplitGb
{
 public:
  SplitGb(std::vector<std::unique_ptr<IncGb>>&& bases);
  SplitGb(const SplitGb& other);
  SplitGb& operator=(const SplitGb& other) = delete;
  bool trivial() const;
  std::vector<CoCoA::RingElem> gens() const;
  const CoCoA::ring& polyRing() const;
  bool containedIn(const CoCoA::RingElem& poly, size_t basisIdx) const;

  // indexing
  size_t numBases() const;
  const IncGb& operator[](size_t basisIdx) const;
  IncGb& operator[](size_t basisIdx);

  // iterator
  using iterator = std::vector<std::unique_ptr<IncGb>>::iterator;
  using const_iterator = std::vector<std::unique_ptr<IncGb>>::const_iterator;
  using value_type = std::vector<std::unique_ptr<IncGb>>::value_type;
  iterator begin() { return d_bases.begin(); }
  iterator end() { return d_bases.end(); }
  const_iterator begin() const { return d_bases.begin(); }
  const_iterator end() const { return d_bases.end(); }

  // expansion
  void addPoly(const CoCoA::RingElem& poly);
  void computeBasis();

 private:
  std::vector<std::unique_ptr<IncGb>> d_bases;
};

/**
 * Construct a model.
 *
 * @param origBases the ideal to find a zero for
 * @param cegar whether to use counter-examples to drive refinement.
 * @param prop whether to use do recursion-free propagation.
 */
std::optional<std::vector<CoCoA::RingElem>> splitModelConstruct(
    const SplitGb& origBases, bool cegar, bool prop);

void checkModel(const SplitGb& origBases,
                const std::vector<CoCoA::RingElem>& model);

/** partial evaluation of polynomials */
std::optional<CoCoA::RingElem> cocoaEval(
    CoCoA::RingElem poly,
    const std::vector<std::optional<CoCoA::RingElem>>& values);

/** total evaluation of polynomials */
CoCoA::RingElem cocoaEval(CoCoA::RingElem poly,
                          const std::vector<CoCoA::RingElem>& values);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__SPLIT_GB_H */

#endif /* CVC5_USE_COCOA */
