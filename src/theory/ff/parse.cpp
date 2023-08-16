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
#include <numeric>
#include <optional>
#include <unordered_map>
#include <unordered_set>

// internal includes
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

namespace parse {

bool add_overflows(uint8_t x, uint8_t y) { return x + y < x; }

template <typename DegreeOp, typename FieldOp>
SpectrumOpt helperResultOp(SpectrumOpt&& a,
                           SpectrumOpt&& b,
                           DegreeOp dOp,
                           FieldOp fOp)
{
  if (!(a.has_value() && b.has_value()))
  {
    // failed child
    return {};
  }
  if (a->degree && b->degree && a->var != b->var)
  {
    // multivariate
    return {};
  }
  uint8_t degree = dOp(a->degree, b->degree);
  if (degree > 2)
  {
    // high-degree
    return {};
  }
  FiniteFieldValue val0 = fOp(a->val0, b->val0);
  FiniteFieldValue val1 = fOp(a->val1, b->val1);
  Node&& var = a->degree ? std::move(a->var) : std::move(b->var);
  return {{var, degree, val0, val1}};
};

/** Subtract spectra */
SpectrumOpt helperResultSub(SpectrumOpt&& a, SpectrumOpt&& b)
{
  return helperResultOp(
      std::move(a),
      std::move(b),
      [](const uint8_t& x, const uint8_t& y) { return std::max(x, y); },
      [](const FiniteFieldValue& x, const FiniteFieldValue& y) {
        return x - y;
      });
};

/** Add spectra */
SpectrumOpt helperResultAdd(SpectrumOpt&& a, SpectrumOpt&& b)
{
  return helperResultOp(
      std::move(a),
      std::move(b),
      [](const uint8_t& x, const uint8_t& y) { return std::max(x, y); },
      [](const FiniteFieldValue& x, const FiniteFieldValue& y) {
        return x + y;
      });
}

/** Multiply spectra */
SpectrumOpt helperResultMul(SpectrumOpt&& a, SpectrumOpt&& b)
{
  return helperResultOp(
      std::move(a),
      std::move(b),
      [](const uint8_t& x, const uint8_t& y) { return x + y; },
      [](const FiniteFieldValue& x, const FiniteFieldValue& y) {
        return x * y;
      });
};

SpectrumOpt spectrum(const Node& t, uint8_t depth)
{
  if (t.getKind() == kind::NOT)
  {
    return {};
  }
  Assert(t.getType().isFiniteField() || t.getKind() == kind::EQUAL) << t;
  if (Theory::isLeafOf(t, THEORY_FF))
  {
    if (t.isConst())
    {
      FiniteFieldValue v = t.getConst<FiniteFieldValue>();
      return {{Node::null(), 0, v, v}};
    }
    else
    {
      const Integer modulus = t.getType().getFfSize();
      return {{t, 1, {1, modulus}, {0, modulus}}};
    }
  }
  switch (t.getKind())
  {
    case kind::FINITE_FIELD_ADD:
    {
      SpectrumOpt acc = spectrum(t[0], depth - 1);
      for (size_t i = 1; i < t.getNumChildren(); ++i)
      {
        acc = helperResultAdd(std::move(acc), spectrum(t[i], depth - 1));
      }
      return acc;
    }
    case kind::EQUAL:
    {
      return helperResultSub(spectrum(t[0], depth - 1),
                             spectrum(t[1], depth - 1));
    }
    case kind::FINITE_FIELD_MULT:
    {
      SpectrumOpt acc = spectrum(t[0], depth - 1);
      for (size_t i = 1; i < t.getNumChildren(); ++i)
      {
        acc = helperResultMul(std::move(acc), spectrum(t[i], depth - 1));
      }
      return acc;
    }
    default: Unreachable() << t.getKind();
  }
  return {};
}

bool zeroConstraint(const Node& fact)
{
  SpectrumOpt r = spectrum(fact);
  return r.has_value() && r->degree == 1 && r->val0.getValue() == 0;
}

bool oneConstraint(const Node& fact)
{
  SpectrumOpt r = spectrum(fact);
  return r.has_value() && r->degree == 1 && r->val1.getValue() == 0;
}

std::optional<Node> bitConstraint(const Node& fact)
{
  SpectrumOpt r = spectrum(fact);
  if (r.has_value() && r->degree == 2 && r->val0.getValue() == 0
      && r->val1.getValue() == 0)
  {
    return {r->var};
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

std::optional<
    std::pair<FiniteFieldValue, std::unordered_map<Node, FiniteFieldValue>>>
sumAffineMonomial(const Node& t)
{
  TypeNode ty = t.getType();
  if (!ty.isFiniteField())
  {
    return {};
  }

  std::unordered_map<Node, FiniteFieldValue> sum{};
  FiniteFieldValue k(0, ty.getFfSize());

  auto linearMonomialOpt = linearMonomial(t);
  if (linearMonomialOpt.has_value())
  {
    sum.insert(linearMonomialOpt.value());
  }
  else if (t.isConst())
  {
    k = t.getConst<FiniteFieldValue>();
  }
  else if (t.getKind() == kind::FINITE_FIELD_ADD)
  {
    // a sum
    for (const auto& child : t)
    {
      if (child.isConst())
      {
        k += child.getConst<FiniteFieldValue>();
        continue;
      }
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
  }
  else
  {
    return {};
  }

  return {{k, std::move(sum)}};
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

std::optional<
    std::pair<FiniteFieldValue, std::unordered_map<Node, FiniteFieldValue>>>
affineEq(const Node& t)
{
  if (t.getKind() == kind::EQUAL && t[0].getType().isFiniteField())
  {
    std::optional<
        std::pair<FiniteFieldValue, std::unordered_map<Node, FiniteFieldValue>>>
        left = sumAffineMonomial(t[0]);
    if (left.has_value())
    {
      std::optional<std::pair<FiniteFieldValue,
                              std::unordered_map<Node, FiniteFieldValue>>>
          right = sumAffineMonomial(t[1]);
      if (right.has_value())
      {
        left->first -= right->first;
        for (const auto& r : right->second)
        {
          increment(left->second, r.first, -r.second);
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
  std::unordered_set<Node> seen{};
  auto it = inv.find(twoToTheI);
  while (it != inv.end())
  {
    if (twoToTheI == negOne)
    {
      // -1 aliased with 2^i; fail.
      return {};
    }
    if (!seen.insert(it->second).second)
    {
      // duplicate variable; fail.
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
  Node negOneVar = inv.at(negOne);

  // if those are everything, this is a bit-sum
  if (bits.size() + 1 != inv.size())
  {
    return {};
  }

  if (!seen.insert(negOneVar).second)
  {
    // duplicate variable; fail.
    return {};
  }

  return {{negOneVar, std::move(bits)}};
}

}  // namespace parse

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
