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
#include "theory/ff/util.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

namespace parse {

bool add_overflows(uint8_t x, uint8_t y) { return x + y < x; }

/**
 * Given spectra for f and g, compute an (optional) spectrum for f @ g, where @ is point-wise operation
 * @param a spectrum for f
 * @param b spectrum for g
 * @param fOp the binary point-wise operator @
 * @param dOp binary operator on uint8_t for computing the degree of f @ g
 *
 * */
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
    case kind::FINITE_FIELD_BITSUM:
    {
      return {};
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

std::optional<std::pair<std::vector<std::pair<Node, FiniteFieldValue>>,
                        std::vector<Node>>>
extractLinearMonomials(const Node& t)
{
  TypeNode ty = t.getType();
  if (!ty.isFiniteField())
  {
    return {};
  }
  if (t.getKind() != kind::FINITE_FIELD_ADD)
  {
    return {};
  }
  std::vector<std::pair<Node, FiniteFieldValue>> monomials{};
  std::vector<Node> otherSummands{};

  for (const Node& summand : t)
  {
    auto monomial = linearMonomial(summand);
    if (monomial.has_value())
    {
      monomials.push_back(std::move(monomial.value()));
    }
    else
    {
      otherSummands.push_back(summand);
    }
  }

  return {{std::move(monomials), std::move(otherSummands)}};
}

std::optional<
    std::pair<std::vector<std::pair<FiniteFieldValue, std::vector<Node>>>,
              std::vector<Node>>>
bitSums(const Node& t, std::unordered_set<Node> isBit)
{
  auto nm = NodeManager::currentNM();
  auto res = extractLinearMonomials(t);
  if (!res.has_value())
  {
    return {};
  }
  TypeNode ty = t.getType();
  const Integer& size = ty.getFfSize();
  auto& [monomials, rest] = res.value();
  Trace("ff::parse::debug") << "bitSums start" << std::endl;
  if (TraceIsOn("ff::parse::debug") && monomials.size())
  {
    Trace("ff::parse::debug") << " term " << t << std::endl;
  }

  std::unordered_map<FiniteFieldValue, Node, FiniteFieldValueHashFunction>
      bitMonomials{};
  std::unordered_set<FiniteFieldValue, FiniteFieldValueHashFunction>
      monomialCoeffs{};
  std::priority_queue<std::pair<Integer, FiniteFieldValue>> q{};
  for (const auto& [var, coeff] : monomials)
  {
    monomialCoeffs.insert(coeff);
    auto it = bitMonomials.find(coeff);
    Trace("ff::parse::debug")
        << "bitMonomial " << coeff << " " << var << std::endl;
    if (it == bitMonomials.end())
    {
      Trace("ff::parse::debug") << " fresh bit" << var << std::endl;
      bitMonomials.insert(it, {coeff, var});
      q.emplace(-coeff.toSignedInteger().abs(), coeff);
    }
    else if (isBit.count(var) && !isBit.count(it->second))
    {
      // they're not a bit, and `var` is, evict them.
      Trace("ff::parse::debug")
          << " " << var << " evicts " << it->second << std::endl;
      rest.push_back(
          nm->mkNode(kind::FINITE_FIELD_MULT, nm->mkConst(coeff), it->second));
      it->second = var;
    }
    else
    {
      Trace("ff::parse::debug")
          << " skipped " << coeff << " " << var << std::endl;
      Trace("ff::parse::debug")
          << "  isBit: " << std::boolalpha << !!isBit.count(var) << std::endl;
      rest.push_back(
          nm->mkNode(kind::FINITE_FIELD_MULT, nm->mkConst(coeff), var));
    }
  }

  std::vector<std::pair<FiniteFieldValue, std::vector<Node>>> bitSums{};
  // TODO: consider other starting constants. Especially to handle gaps...
  FiniteFieldValue two(2, size);
  // look for runs k*x, 2k*y, 4k*z, ...
  while (!q.empty())
  {
    FiniteFieldValue k = q.top().second;
    q.pop();
    FiniteFieldValue acc = k;
    std::vector<Node> bits{};
    std::vector<Node> erasedSummands{};
    while (bitMonomials.count(acc))
    {
      auto var = bitMonomials.at(acc);
      bits.push_back(var);
      erasedSummands.push_back(
          nm->mkNode(kind::FINITE_FIELD_MULT, nm->mkConst(acc), var));
      bitMonomials.erase(acc);
      acc *= two;
    }
    if (monomialCoeffs.count(acc))
    {
      monomialCoeffs.erase(acc);
    }
    if (bits.size() > 1)
    {
      bitSums.emplace_back(k, std::move(bits));
    }
    else
    {
      for (auto& summand : erasedSummands)
      {
        rest.push_back(std::move(summand));
      }
    }
  }

  for (const auto& [coeff, var] : bitMonomials)
  {
    rest.push_back(
        nm->mkNode(kind::FINITE_FIELD_MULT, nm->mkConst(coeff), var));
  }
  return {{std::move(bitSums), std::move(rest)}};
}

std::optional<Node> disjunctiveBitConstraint(const Node& t)
{
  if (t.getKind() == kind::OR && t.getNumChildren() == 2
      && t[0].getKind() == kind::EQUAL && t[1].getKind() == kind::EQUAL
      && t[0][1].getType().isFiniteField() && t[1][0].getType().isFiniteField())
  {
    using theory::ff::parse::oneConstraint;
    using theory::ff::parse::zeroConstraint;
    if ((oneConstraint(t[0]) && zeroConstraint(t[1]))
        || (oneConstraint(t[1]) && zeroConstraint(t[0])))
    {
      using theory::ff::parse::spectrum;
      return {spectrum(t[0])->var};
    }
  }
  return {};
}

std::optional<std::pair<Node, Node>> zeroProduct(const Node& f)
{
  if (f.getKind() != kind::EQUAL)
  {
    return {};
  }
  if (isFfZero(f[0]) && f[1].getKind() == kind::FINITE_FIELD_MULT)
  {
    return {{f[0], f[1]}};
  }
  else if (isFfZero(f[1]) && f[0].getKind() == kind::FINITE_FIELD_MULT)
  {
    return {{f[1], f[0]}};
  }
  else
  {
    return {};
  }
}

}  // namespace parse

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
