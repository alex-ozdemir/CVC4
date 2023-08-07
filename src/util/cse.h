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
 * common subexpression elimination (greedy)
 */

#include "cvc5_private.h"

#ifndef CVC5__UTIL__CSE_H
#define CVC5__UTIL__CSE_H

// external includes

// std includes
#include <unordered_map>

// internal includes
#include "expr/node.h"

namespace cvc5::internal {
namespace util {

/** EGraph with explicit representative control */
class EGraph
{
 public:
  /** Ensure elem is in the graph */
  void add(const Node& elem);
  /** Make rep the representative of elem */
  void setRep(const Node& elem, const Node& rep);
  /** Get the representative of elem */
  const Node& getRep(const Node& elem);
  /** Replace all descendents of t with their representatives */
  Node rewrite(const Node& t);

 private:
  std::unordered_map<Node, Node> d_reps{};
};

/** Given an n-ary node, rewrite with elements [i, i + size) in an inner
 * (nested) node.
 *
 * @param n a node (x[0] ... x[N-1])
 * @return a node t = (x[i] ... x[i+size]) and a node
 *         a node (x[0] ... x[i-1] t x[i+size+1] ... x[N-1])
 *
 *
 * @note asserts size > 1
 * @note if size is equal to n's size, returns (t, t)
 */
std::pair<Node, Node> stratify(const Node& n, size_t i, size_t size);

/** Rewrite t using greedy common subexpression elimination for kind k.
 *
 * Only does *associative* CSE. Never re-orders children.
 *
 * Algorithm:
 *
 * @verbatim
 * * while some pair of k-kinded nodes has a common sub-string of children:
 *   * (of length > 1)
 *   * choose the pair to maximize (substring size, -len(node0)-len(node1))
 *   * extract that common sub-string
 * @endverbatim
 * */
Node greedyCse(const Node& t, Kind k);

/** Return the longest common sub-string of child nodes in a, b.
 *
 * @param a a node
 * @param b a node
 * @return (size, a_i, b_i)
 *         size: the size of the sub-string
 *         a_i: its first index in a
 *         b_i: its first index in b
 * */
std::tuple<size_t, size_t, size_t> lcss(const Node& a, const Node& b);

}  // namespace util
}  // namespace cvc5::internal

#endif /* CVC5__UTIL__CSE_H */
