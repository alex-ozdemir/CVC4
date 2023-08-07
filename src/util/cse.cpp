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

#include "util/cse.h"

// external includes

// std includes
#include <functional>
#include <queue>
#include <utility>
#include <vector>

// internal includes
#include "expr/node_traversal.h"

namespace cvc5::internal {
namespace util {

using NMap = std::unordered_map<Node, Node>;
using NSet = std::unordered_set<Node>;

void EGraph::add(const Node& elem)
{
  auto it = d_reps.find(elem);
  if (it == d_reps.end())
  {
    d_reps.insert(it, {elem, elem});
  }
}

void EGraph::setRep(const Node& elem, const Node& rep)
{
  auto it = d_reps.find(elem);
  Assert(it != d_reps.end());
  Assert(d_reps.count(rep));
  it->second = rep;
}

const Node& EGraph::getRep(const Node& elem)
{
  std::vector<NMap::iterator> steps{};
  auto it = d_reps.find(elem);
  Assert(it != d_reps.end());
  // chase path
  while (it->second != it->first)
  {
    steps.push_back(it);
    it = d_reps.find(it->second);
    Assert(it != d_reps.end());
  }
  // path compression
  for (auto& step : steps)
  {
    step->second = it->second;
  }
  return it->second;
}

Node EGraph::rewrite(const Node& t)
{
  // (node, childrenPushed)
  std::vector<std::pair<Node, bool>> q{{getRep(t), false}};
  NMap cache{};
  while (!q.empty())
  {
    const auto [n, childrenPushed] = q.back();
    q.pop_back();
    Assert(d_reps.at(n) == n);
    if (cache.count(n))
    {
      continue;
    }
    if (childrenPushed)
    {
      Node n_new = n;
      if (n.getNumChildren())
      {
        NodeBuilder nb(n.getKind());
        for (const auto& c : n)
        {
          nb << cache.at(getRep(c));
        }
        n_new = nb;
      }
      cache.insert({n, n_new});
    }
    else
    {
      q.push_back({n, true});
      for (const auto& c : n)
      {
        q.push_back({getRep(c), false});
      }
    }
  }
  return cache.at(t);
}

std::pair<Node, Node> stratify(const Node& n, size_t i, size_t size)
{
  if (size == n.getNumChildren())
  {
    return {n, n};
  }
  else
  {
    Assert(size < n.getNumChildren());
    NodeBuilder innerNb(n.getKind());
    Node inner;
    NodeBuilder outerNb(n.getKind());
    for (size_t j = 0; j < i; ++j)
    {
      outerNb << n[j];
    }
    for (size_t j = i; j < i + size; ++j)
    {
      innerNb << n[j];
    }
    inner = innerNb;
    outerNb << inner;
    for (size_t j = i + size; j < n.getNumChildren(); ++j)
    {
      outerNb << n[j];
    }
    return {inner, outerNb};
  }
}

size_t getDefault(std::unordered_map<size_t, size_t>& map,
                  size_t key,
                  size_t defaultValue)
{
  auto it = map.find(key);
  return it == map.end() ? defaultValue : it->second;
}

std::tuple<size_t, size_t, size_t> lcss(const Node& a, const Node& b)
{
  // a DP to compute the longest common suffices of a[..ai]  and b[..bi]
  Assert(a.getKind() == b.getKind());
  // map: a_i -> b_i -> common suffix length of a[..ai] and b[..bi]
  std::unordered_map<size_t, std::unordered_map<size_t, size_t>> lens{};
  std::tuple<size_t, size_t, size_t> ret{0, 0, 0};
  for (size_t ai = 0; ai < a.getNumChildren(); ++ai)
  {
    lens[ai];
    for (size_t bi = 0; bi < b.getNumChildren(); ++bi)
    {
      if (a[ai] == b[bi])
      {
        size_t thisLen = 1;
        if (ai > 0 && bi > 0)
        {
          thisLen = getDefault(lens[ai - 1], bi - 1, 0) + 1;
        }
        lens[ai][bi] = thisLen;
        if (thisLen > std::get<0>(ret))
        {
          ret = {thisLen, ai - thisLen + 1, bi - thisLen + 1};
        }
      }
    }
    if (ai > 0)
    {
      lens.erase(ai - 1);
    }
  }

  return ret;
}

Node greedyCse(const Node& t, Kind k)
{
  // nodes of kind k
  std::vector<Node> nodes{};
  // egraph; will update as we optimize
  EGraph eg{};
  // nodes that are part of the curre
  NSet active{};
  for (const auto& n : NodeDfsIterable(t))
  {
    eg.add(n);
    if (n.getKind() == k)
    {
      active.insert(n);
      nodes.push_back(n);
    }
  }

  // initialize queue of nodes to intersect
  using Key = std::tuple<ssize_t, ssize_t>;
  using QElem = std::tuple<Key, size_t, size_t, size_t, Node, Node>;
  const auto mkKey = [](size_t size, const Node& a, const Node& b) {
    // take bigger intersections first, followed by smaller intersect-ees.
    return Key(size, -a.getNumChildren() - b.getNumChildren());
  };
  std::priority_queue<QElem> q{};
  for (size_t i = 0; i < nodes.size(); ++i)
  {
    for (size_t j = 0; j < i; ++j)
    {
      const Node& a = nodes[i];
      const Node& b = nodes[j];
      const auto [size, ai, bi] = lcss(a, b);
      if (size > 1)
      {
        q.emplace(mkKey(size, a, b), size, ai, bi, a, b);
      }
    }
  }

  // intersect nodes until queue is empty
  while (!q.empty())
  {
    const auto [_, len, xi, yi, x, y] = q.top();
    q.pop();
    if (!active.count(x) || !active.count(y))
    {
      // skip now-inactive nodes
      continue;
    }

    // do the intersection
    const auto [cse_in_x, x_new] = stratify(x, xi, len);
    const auto [cse_in_y, y_new] = stratify(y, yi, len);
    Assert(cse_in_x == cse_in_y);
    const auto& cse = cse_in_x;

    // update egraph
    eg.add(x_new);
    eg.add(y_new);
    eg.add(cse);
    eg.setRep(x, x_new);
    eg.setRep(y, y_new);

    // add new pairs
    active.erase(x);
    active.erase(y);
    for (const Node& a : {cse, x_new, y_new})
    {
      for (const Node& b : active)
      {
        if (a != b)
        {
          const auto [size, ai, bi] = lcss(a, b);
          if (size > 1)
          {
            q.emplace(mkKey(size, a, b), size, ai, bi, a, b);
          }
        }
      }
      active.insert(a);
    }
  }

  return eg.rewrite(t);
}

}  // namespace util
}  // namespace cvc5::internal
