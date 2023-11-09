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
#include <CoCoA/ideal.H>
#include <CoCoA/ring.H>
#include <CoCoA/symbol.H>

// std includes
#include <memory>
#include <optional>
#include <unordered_set>
#include <variant>
#include <vector>

// internal includes
#include "theory/ff/cocoa.h"
#include "theory/ff/cocoa_util.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/** partial evaluation of polynomials */
std::optional<CoCoA::RingElem> cocoaEval(
    CoCoA::RingElem poly,
    const std::vector<std::optional<CoCoA::RingElem>>& values);

/** total evaluation of polynomials */
CoCoA::RingElem cocoaEval(CoCoA::RingElem poly,
                          const std::vector<CoCoA::RingElem>& values);

/** Wraps a CoCoA GBasis, but supports an empty basis. */
class Gb
{
 public:
  Gb();
  Gb(const std::vector<CoCoA::RingElem>& generators);
  bool contains(const CoCoA::RingElem& p) const;
  bool isWholeRing() const;
  CoCoA::RingElem reduce(const CoCoA::RingElem& p) const;
  bool zeroDimensional() const;
  CoCoA::RingElem minimalPolynomial(const CoCoA::RingElem& p) const;
  const std::vector<CoCoA::RingElem>& basis() const;

 private:
  std::optional<CoCoA::ideal> d_ideal;
  std::vector<CoCoA::RingElem> d_basis;
};

class BitProp
{
 public:
  BitProp(const std::vector<Node>& facts, CocoaEncoder& encoder);
  BitProp();
  std::vector<CoCoA::RingElem> getBitEqualities(
      const std::vector<Gb>& splitBasis);

 private:
  std::unordered_set<Node> d_bits;
  std::vector<Node> d_bitsums;
  CocoaEncoder* d_enc;
};

bool admit(size_t i, const CoCoA::RingElem& p);

std::vector<Gb> splitGb(
    const std::vector<std::vector<CoCoA::RingElem>>& generatorSets,
    BitProp& bitProp);

using SplitGb2 = std::vector<Gb>;

std::variant<std::vector<CoCoA::RingElem>, CoCoA::RingElem, bool>
splitZeroExtend(const std::vector<CoCoA::RingElem>& origPolys,
                const SplitGb2&& curBases,
                const PartialRoot&& curR,
                const BitProp& bitProp);

std::optional<std::vector<CoCoA::RingElem>> splitFindZero(
    SplitGb2&& splitBasis, CoCoA::ring polyRing, BitProp& bitProp);

std::optional<std::unordered_map<Node, FiniteFieldValue>> splitFindZero(
    const std::vector<Node>& facts, const FfSize& size);

void checkModel(const SplitGb2& origBases,
                const std::vector<CoCoA::RingElem>& model);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__SPLIT_GB_H */

#endif /* CVC5_USE_COCOA */
