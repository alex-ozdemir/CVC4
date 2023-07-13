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
 * parsing structured field terms
 */

#include "theory/ff/parse.h"

// external includes

// std includes
#include <optional>
#include <unordered_map>

// internal includes

namespace cvc5::internal {
namespace theory {
namespace ff {

namespace parse {

std::optional<Node> square(const Node& t)
{
  if (t.getKind() == kind::FINITE_FIELD_MULT && t[0].isVar() && t[0] == t[1])
  {
    return t[0];
  }
  return {};
}

std::optional<Node> xMinusOne(const Node& t)
{
  if (t.getKind() == kind::FINITE_FIELD_ADD && t.getNumChildren() == 2)
  {
    if (t[0].isVar() && t[1].isConst()
        && t[1].getConst<FiniteFieldValue>().toSignedInteger() == -1)
    {
      return t[0];
    }
    if (t[1].isVar() && t[0].isConst()
        && t[0].getConst<FiniteFieldValue>().toSignedInteger() == -1)
    {
      return t[1];
    }
  }
  return {};
}

std::optional<Node> xXMinusOne(const Node& t)
{
  if (t.getKind() == kind::FINITE_FIELD_MULT && t.getNumChildren() == 2)
  {
    if (t[0].isVar())
    {
      std::optional<Node> rightX = xMinusOne(t[1]);
      if (rightX.has_value() && t[0] == rightX.value())
      {
        return t[0];
      }
    }
    else if (t[1].isVar())
    {
      std::optional<Node> leftX = xMinusOne(t[0]);
      if (leftX.has_value() && t[1] == leftX.value())
      {
        return t[1];
      }
    }
  }
  return {};
}

std::optional<Node> bitConstraint(const Node& fact)
{
  if (fact.getKind() == kind::EQUAL && fact[0].getType().isFiniteField())
  {
    if (fact[0].isVar())
    {
      if (fact[0] == square(fact[1]))
      {
        // (= x (ff.mul x x))
        return fact[0];
      }
    }
    if (fact[1].isVar())
    {
      if (fact[1] == square(fact[0]))
      {
        // (= (ff.mul x x) x)
        return fact[1];
      }
    }
    if (fact[0].isConst()
        && fact[0].getConst<FiniteFieldValue>().toInteger() == 0)
    {
      std::optional<Node> opt = xXMinusOne(fact[1]);
      if (opt.has_value())
      {
        // (= 0 (ff.mul x (ff.add x -1)))
        return opt;
      }
    }
    if (fact[1].isConst()
        && fact[1].getConst<FiniteFieldValue>().toInteger() == 0)
    {
      std::optional<Node> opt = xXMinusOne(fact[0]);
      if (opt.has_value())
      {
        // (= (ff.mul x (ff.add x -1)) 0)
        return opt;
      }
    }
  }
  return {};
}

std::optional<std::pair<Node, FiniteFieldValue>> varNeValue(const Node& fact)
{
  if (fact.getKind() == kind::NOT && fact[0].getKind() == kind::EQUAL
      && fact[0][0].getType().isFiniteField())
  {
    if (fact[0][0].isVar() && fact[0][1].isConst())
    {
      return {{fact[0][0], fact[0][1].getConst<FiniteFieldValue>()}};
    }
    else if (fact[0][1].isVar() && fact[0][0].isConst())
    {
      return {{fact[0][1], fact[0][0].getConst<FiniteFieldValue>()}};
    }
  }
  return {};
}

std::optional<std::pair<Node, FiniteFieldValue>> linearMonomial(const Node& t)
{
  TypeNode ty = t.getType();
  if (!ty.isFiniteField())
  {
    return {};
  }
  const Integer& p = ty.getFfSize();

  // X
  if (t.isVar())
  {
    return {{t, FiniteFieldValue(1, p)}};
  }

  // (ff.neg X)
  if (t.getKind() == kind::FINITE_FIELD_NEG && t[0].isVar())
  {
    return {{t[0], FiniteFieldValue(-1, p)}};
  }

  // (ff.mul ? ?)
  if (t.getKind() == kind::FINITE_FIELD_MULT && t.getNumChildren() == 2)
  {
    // (ff.mul k X)
    if (t[0].isConst() && t[1].isVar())
    {
      return {{t[1], t[0].getConst<FiniteFieldValue>()}};
    }

    // (ff.mul X k)
    if (t[1].isConst() && t[0].isVar())
    {
      return {{t[0], t[1].getConst<FiniteFieldValue>()}};
    }
  }

  return {};
}

namespace {

/** Set map[key] += value; default-initializing to zero */
void increment(std::unordered_map<Node, FiniteFieldValue>& map,
               const Node& key,
               const FiniteFieldValue& value)
{
  auto it = map.find(key);
  if (it == map.end())
  {
    map.insert(it, {key, value});
  }
  else
  {
    it->second += value;
  }
}

}  // namespace

std::optional<std::unordered_map<Node, FiniteFieldValue>> sumLinearMonomial(
    const Node& t)
{
  TypeNode ty = t.getType();
  if (!ty.isFiniteField())
  {
    return {};
  }

  std::unordered_map<Node, FiniteFieldValue> sum{};

  auto linearMonomialOpt = linearMonomial(t);
  if (linearMonomialOpt.has_value())
  {
    sum.insert(linearMonomialOpt.value());
    return std::move(sum);
  }

  if (t.getKind() == kind::FINITE_FIELD_ADD)
  {
    // a sum
    for (const auto& child : t)
    {
      linearMonomialOpt = linearMonomial(child);
      if (linearMonomialOpt.has_value())
      {
        increment(sum, linearMonomialOpt->first, linearMonomialOpt->second);
      }
      else
      {
        return {};
      }
    }
    return std::move(sum);
  }
  else if (t.isConst() && t.getConst<FiniteFieldValue>().getValue().isZero())
  {
    // just a zero
    return std::move(sum);
  }

  return {};
}

std::optional<std::unordered_map<Node, FiniteFieldValue>> linearEq(
    const Node& t)
{
  if (t.getKind() == kind::EQUAL && t[0].getType().isFiniteField())
  {
    std::optional<std::unordered_map<Node, FiniteFieldValue>> left =
        sumLinearMonomial(t[0]);
    if (left.has_value())
    {
      std::optional<std::unordered_map<Node, FiniteFieldValue>> right =
          sumLinearMonomial(t[1]);
      if (right.has_value())
      {
        for (const auto& r : right.value())
        {
          increment(left.value(), r.first, -r.second);
        }
        return std::move(left.value());
      }
    }
  }
  return {};
}

void normalizeLinearEq(std::unordered_map<Node, FiniteFieldValue>& linearEq)
{
  // remove zeros
  for (auto it = linearEq.begin(); it != linearEq.end();)
  {
    if (it->second.getValue().isZero())
    {
      it = linearEq.erase(it);
    }
    else
    {
      ++it;
    }
  }

  // count positives
  size_t positive = 0;
  for (const auto& monomial : linearEq)
  {
    if (monomial.second.toSignedInteger() > 0)
    {
      positive += 1;
    }
  }

  // flip if positives are a minority
  if (positive * 2 < linearEq.size())
  {
    for (auto& monomial : linearEq)
    {
      monomial.second = -monomial.second;
    }

#ifdef CVC5_ASSERTIONS
    // assert that positives are not a minority
    positive = 0;
    for (const auto& monomial : linearEq)
    {
      if (monomial.second.toSignedInteger() > 0)
      {
        positive += 1;
      }
    }
    Assert(positive * 2 >= linearEq.size());
#endif  // CVC5_ASSERTIONS
  }
}

std::optional<std::pair<Node, std::vector<Node>>> bitsConstraint(
    const Node& fact)
{
  // parse and normalize the linear equality.
  auto e = linearEq(fact);
  if (!e.has_value())
  {
    return {};
  }
  normalizeLinearEq(e.value());

  // invert the map
  std::unordered_map<FiniteFieldValue, Node, FiniteFieldValueHashFunction>
      inv{};
  for (const auto& monomial : e.value())
  {
    if (!inv.insert({monomial.second, monomial.first}).second)
    {
      // duplicate coefficient; fail.
      return {};
    }
  }

  if (inv.size() == 0)
  {
    // empty; fail
    return {};
  }

  // find powers of two
  FiniteFieldValue twoToTheI =
      FiniteFieldValue(1, inv.begin()->first.getFieldSize());
  FiniteFieldValue two = FiniteFieldValue(2, inv.begin()->first.getFieldSize());
  FiniteFieldValue negOne =
      FiniteFieldValue(-1, inv.begin()->first.getFieldSize());
  std::vector<Node> bits{};
  auto it = inv.find(twoToTheI);
  while (it != inv.end())
  {
    if (twoToTheI == negOne)
    {
      // -1 aliased with 2^i; fail.
      return {};
    }
    bits.push_back(it->second);
    twoToTheI *= two;
    it = inv.find(twoToTheI);
  }

  // find -1
  if (!inv.count(negOne))
  {
    return {};
  }

  // if those are everything, this is a bit-sum
  if (bits.size() + 1 != inv.size())
  {
    return {};
  }

  return {{inv.at(negOne), std::move(bits)}};
}

}  // namespace parse

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
