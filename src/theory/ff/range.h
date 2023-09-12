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
 * range-based ff sub-solber
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__RANGE_H
#define CVC5__THEORY__FF__RANGE_H

// external includes

// std includes
#include <unordered_map>
#include <unordered_set>

// internal includes
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/ff/to_int.h"
#include "theory/ff/util.h"
#include "util/finite_field_value.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

struct Range
{
  Range(const Integer& singleton);
  Range(const Integer& lo, const Integer& hi);
  Range operator+(const Range& other) const;
  Range operator*(const Range& other) const;
  Range operator*(const Integer& other) const;
  Range operator-() const;
  Range operator-(const Range& other) const;
  bool operator==(const Range& other) const;
  bool operator!=(const Range& other) const;
  Range intersect(const Range& other) const;
  bool contains(const Range& other) const;
  bool isZero() const;
  /** the quotient of this range by `other`, rounded down */
  Range floorDivideQuotient(const Integer& other) const;

  /** inclusive; possibly negative; d_lo <= d_hi */
  Integer d_lo, d_hi;
};

class RangeSolver : EnvObj, FieldObj
{
 public:
  RangeSolver(Env& env, const Integer& p);
  void assertFact(TNode fact);
  // TODO: SAT might have an empty model.
  std::pair<Result, std::unordered_map<Node, FiniteFieldValue>> check();
  std::pair<Result, std::unordered_map<Node, FiniteFieldValue>> checkHelper(bool unsound, size_t timeoutMs);
  Range getRange(TNode term);
  void clear();

 private:

  /** Ranges detected. */
  std::unordered_map<Node, Range> d_assertedRanges{};
  /** Ranges computed. */
  std::unordered_map<Node, Range> d_ranges{};
  /** Non-range facts. */
  std::vector<Node> d_facts{};
};

std::ostream& operator<<(std::ostream& o, const Range& r);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__RANGE_H */
