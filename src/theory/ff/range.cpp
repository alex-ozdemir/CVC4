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

#include "theory/ff/range.h"

// external includes
#include <z3++.h>

// std includes
#include <algorithm>
#include <numeric>
#include <unordered_map>

// internal includes
#include "context/cdhashmap.h"
#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "smt/env.h"
#include "smt/env_obj.h"
#include "theory/ff/parse.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

RangeSolver::RangeSolver(Env& env, const Integer& p) : EnvObj(env), d_p(p){};

void RangeSolver::assertFact(TNode fact)
{
  // is this a bit-constraint?
  std::optional<Node> range = parse::bitConstraint(fact);
  if (range.has_value())
  {
    const Node& var = range.value();
    auto it = d_assertedRanges.find(var);
    Range r(0, 1);
    if (it != d_assertedRanges.end())
    {
      r = it->second.intersect(r);
    }
    d_assertedRanges.insert({var, r});
    Trace("ff::range::bounds") << "range " << var << ": " << r << std::endl;
    return;
  }

  // is this a range-shrinking disequality?
  if (options().ff.ffRangeNe)
  {
    std::optional<std::pair<Node, FiniteFieldValue>> varNeValue =
        parse::varNeValue(fact);
    if (varNeValue.has_value())
    {
      auto it = d_assertedRanges.find(varNeValue->first);
      if (it != d_assertedRanges.end())
      {
        if (it->second.d_lo == varNeValue->second.toInteger())
        {
          it->second.d_lo += 1;
          Trace("ff::range::bounds") << "tighten to range " << varNeValue->first
                                     << ": " << it->second << std::endl;
          return;
        }
        if (it->second.d_hi == varNeValue->second.toInteger())
        {
          it->second.d_hi -= 1;
          Trace("ff::range::bounds") << "tighten to range " << varNeValue->first
                                     << ": " << it->second << std::endl;
          return;
        }
      }
    }
  }

  savePlainFact(fact);
  Trace("ff::range") << "fact " << fact << std::endl;
}

std::unordered_map<Node, FiniteFieldValue> RangeSolver::check()
{
  Range bitRange = Range(0, 1);
  z3::context ctx;
  z3::expr zero = ctx.int_val(0);
  z3::expr one = ctx.int_val(1);
  z3::expr p = ctx.int_val(d_p.toString().c_str());
  size_t qI = 0;
  size_t accI = 0;
  std::unordered_map<Node, z3::expr> ints{};
  std::vector<z3::expr> assertions{};

  // ranges
  for (const auto& i : d_assertedRanges)
  {
    z3::expr var = ctx.int_const(i.first.getName().c_str());
    // maybe redudant
    ints.insert({i.first, var});
    z3::expr lo = ctx.int_val(i.second.d_lo.toString().c_str());
    z3::expr hi = ctx.int_val(i.second.d_hi.toString().c_str());
    assertions.push_back((var >= lo) & (var <= hi));
  }

  // map: cvc5 var -> (z3 expr, bit number)
  std::unordered_map<Node, std::pair<z3::expr, size_t>> varsToBits{};

  // facts
  for (const auto& f : d_facts)
  {
    for (TNode current :
         NodeDfsIterable(f, VisitOrder::POSTORDER, [&ints](TNode nn) {
           bool ffFact =
               nn.getKind() == kind::NOT || nn.getKind() == kind::EQUAL;
           bool ffTerm = nn.getType().isFiniteField();
           return ints.count(nn) || !(ffFact || ffTerm);
         }))
    {
      Assert(!ints.count(current));
      z3::expr e = zero;
      if (current.isVar())
      {
        e = ctx.int_const(current.getName().c_str());
        assertions.push_back((e >= 0) & (e < p));
      }
      else if (current.isConst())
      {
        e = ctx.int_val(current.getConst<FiniteFieldValue>()
                            .toInteger()
                            .toString()
                            .c_str());
      }
      else if (current.getKind() == kind::FINITE_FIELD_ADD)
      {
        bool stdAdd = true;
        if (options().ff.ffElimBits)
        {
          // look for bit-sums in the addition; replace them with ranges.
          auto res = parse::bitSums(current, [this, &bitRange](const Node& x) {
            bool isBit = d_parentsInFacts.at(x) == 1 && bitRange == getRange(x);
            Trace("ff::range::isBit")
                << " isBit " << x << " : " << isBit << std::endl;
            return isBit;
          });
          if (res.has_value() && !res.value().first.empty())
          {
            auto& [bitSums, rest] = res.value();
            e = zero;
            for (const auto& r : rest)
            {
              // rw because the parser mangles
              e = e + ints.at(rewrite(r));
            }
            for (const auto& [coeff, bits] : bitSums)
            {
              z3::expr acc = ctx.int_const(
                  (std::string("__acc") + std::to_string(accI)).c_str());
              accI++;
              z3::expr k = ctx.int_val(coeff.toInteger().toString().c_str());
              e = e + acc * k;
              if (TraceIsOn("ff::range"))
              {
                Trace("ff::range") << "bitsum: " << coeff << " * bitsum(";
                for (const auto& b : bits)
                {
                  Trace("ff::range") << b << ",";
                }
                Trace("ff::range") << ")" << std::endl;
              }
              for (size_t i = 0; i < bits.size(); ++i)
              {
                varsToBits.insert({bits[i], {acc, i}});
              }
              z3::expr upper =
                  ctx.int_val(Integer(2).pow(bits.size()).toString().c_str());
              assertions.push_back((acc >= 0) && (acc < upper));
            }
            stdAdd = false;
          }
        }

        if (stdAdd)
        {
          Trace("ff::range::bitsum")
              << "sum with no bits: " << current << std::endl;
          e = zero;
          for (const auto& child : current)
          {
            e = e + ints.at(child);
          }
        }
      }
      else if (current.getKind() == kind::FINITE_FIELD_MULT)
      {
        e = one;
        for (const auto& child : current)
        {
          e = e * ints.at(child);
        }
      }
      else if (current.getKind() == kind::EQUAL
               || current.getKind() == kind::NOT)
      {
        // pass
      }
      else
      {
        Unimplemented() << "Unsupported kind: " << current.getKind();
      }
      ints.insert({current, e});
    }
    if (f.getKind() == kind::EQUAL)
    {
      // equality: left - right = q * p
      z3::expr q =
          ctx.int_const((std::string("__q") + std::to_string(qI)).c_str());
      qI++;
      assertions.push_back((ints.at(f[0]) - ints.at(f[1])) == q * p);

      if (options().ff.ffQuotientRanges)
      {
        // use range analysis to bound q tightly.
        auto diffRange = getRange(f[0]) - getRange(f[1]);
        Trace("ff::range") << "range " << f << ": " << diffRange << std::endl;
        auto lo = ctx.int_val(
            diffRange.d_lo.ceilingDivideQuotient(d_p).toString().c_str());
        auto hi = ctx.int_val(
            diffRange.d_hi.ceilingDivideQuotient(d_p).toString().c_str());
        assertions.push_back((q >= lo) && (q <= hi));
      }
    }
    else
    {
      // inequality: (left - right) * inv = 1 + q * p
      Assert(f.getKind() == kind::NOT && f[0].getKind() == kind::EQUAL);
      Node e = f[0];
      z3::expr q =
          ctx.int_const((std::string("__q") + std::to_string(qI)).c_str());
      z3::expr i =
          ctx.int_const((std::string("__i") + std::to_string(qI)).c_str());
      qI++;
      assertions.push_back((ints.at(e[0]) - ints.at(e[1])) * i == one + q * p);

      assertions.push_back((i >= zero) && (i < p));
    }
  }

  z3::solver s{ctx};
  for (const auto& a : assertions)
  {
    Trace("ff::range::assert") << "to z3: " << a << std::endl;
    // s.add(a);
  }
  z3::check_result r = s.check(assertions.size(), &assertions[0]);
  switch (r)
  {
    case z3::check_result::sat:
    {
      std::unordered_map<Node, FiniteFieldValue> model{};
      for (const auto& it : ints)
      {
        if (it.first.isVar() && !varsToBits.count(it.first))
        {
          // Not sure what to do with the argument to get_decimal_string.
          auto val = FiniteFieldValue(
              Integer(
                  s.get_model().eval(ints.at(it.first)).get_decimal_string(0)),
              d_p);
          Trace("ff::range::model") << "model " << it.first << ": "
                                    << val.toSignedInteger() << std::endl;
          model.insert({it.first, val});
        }
      }
      for (const auto& [var, entry] : varsToBits)
      {
        const auto& [z3var, bitI] = entry;
        Integer z3val =
            Integer(s.get_model().eval(z3var).get_decimal_string(0));
        auto val = FiniteFieldValue(z3val.isBitSet(bitI), d_p);
        Trace("ff::range::model")
            << "model " << var << ": " << val.toSignedInteger() << std::endl;
        Assert(!model.count(var));
        model.insert({var, val});
      }

      return model;
    }
    case z3::check_result::unsat:
    {
      if (TraceIsOn("ff::range::core"))
      {
        Trace("ff::range::core") << "Core:" << std::endl;
        for (const auto& c : s.unsat_core())
        {
          Trace("ff::range::core") << " " << c << std::endl;
        }
      }
      return {};
    }
    case z3::check_result::unknown:
    {
      Unimplemented() << "unknown";
    }
    default: Unreachable() << "error";
  }
}

Range RangeSolver::getRange(TNode term)
{
  Assert(term.getType().isFiniteField());
  // persisting this would tricky, since tighter leaf ranges invalidate entries
  for (TNode current :
       NodeDfsIterable(term, VisitOrder::POSTORDER, [this](TNode nn) {
         return !nn.getType().isFiniteField() || d_ranges.count(nn);
       }))
  {
    Assert(current.getType().isFiniteField());
    Range r{0};
    if (d_assertedRanges.count(current))
    {
      r = d_assertedRanges.find(current)->second;
    }
    else if (current.isConst())
    {
      r = Range(current.getConst<FiniteFieldValue>().toInteger());
    }
    else if (current.getKind() == kind::FINITE_FIELD_ADD)
    {
      r = std::accumulate(
          current.begin(),
          current.end(),
          Range(0),
          [this](Range acc, TNode child) { return acc + d_ranges.at(child); });
    }
    else if (current.getKind() == kind::FINITE_FIELD_MULT)
    {
      r = std::accumulate(
          current.begin(),
          current.end(),
          Range(1),
          [this](Range acc, TNode child) { return acc * d_ranges.at(child); });
    }
    else if (current.getKind() == kind::FINITE_FIELD_NEG)
    {
      r = -d_ranges.at(current[0]);
    }
    else if (current.isVar() || current.getKind() == kind::APPLY_UF)
    {
      r = Range(0, d_p - 1);
    }
    else
    {
      Unimplemented() << "Unsupported kind: " << current.getKind();
    }
    Trace("ff::range::debug") << "range " << current << ": " << r << std::endl;
    d_ranges.insert({current, r});
  }
  return d_ranges.at(term);
}

void RangeSolver::clear()
{
  d_assertedRanges.clear();
  d_ranges.clear();
  d_facts.clear();
}

void RangeSolver::savePlainFact(const Node& fact)
{
  // it's a plain fact; update parent counts
  // enumerate (parent, child) pairs
  for (TNode parent :
       NodeDfsIterable(fact, VisitOrder::POSTORDER, [this](TNode n) {
         // skip N as a parent if N has already been a child
         return d_parentsInFacts.count(n);
       }))
  {
    for (const Node& child : parent)
    {
      ++d_parentsInFacts.at(child);
    }
    d_parentsInFacts.insert({parent, 0});
  }

  d_facts.emplace_back(fact);
}

Range::Range(const Integer& singleton) : d_lo(singleton), d_hi(singleton){};

Range::Range(const Integer& lo, const Integer& hi) : d_lo(lo), d_hi(hi){};

Range Range::operator+(const Range& other) const
{
  return Range(d_lo + other.d_lo, d_hi + other.d_hi);
}

Range Range::operator*(const Range& other) const
{
  Integer a = d_lo * other.d_lo;
  Integer b = d_lo * other.d_hi;
  Integer c = d_hi * other.d_lo;
  Integer d = d_hi * other.d_hi;
  return Range(std::min(a, std::min(b, std::min(c, d))),
               std::max(a, std::max(b, std::max(c, d))));
}

Range Range::operator-() const { return Range(-d_hi, -d_lo); }

Range Range::operator-(const Range& other) const
{
  return Range(d_lo - other.d_hi, d_hi - other.d_lo);
}

bool Range::operator==(const Range& other) const
{
  return d_lo == other.d_lo && d_hi == other.d_hi;
}

bool Range::operator!=(const Range& other) const
{
  return d_lo != other.d_lo || d_hi != other.d_hi;
}

Range Range::intersect(const Range& other) const
{
  return Range(std::max(d_lo, other.d_lo), std::min(d_hi, other.d_hi));
}

bool Range::contains(const Range& other) const
{
  return d_lo <= other.d_lo && d_hi >= other.d_hi;
}

std::ostream& operator<<(std::ostream& o, const Range& r)
{
  return o << "[" << r.d_lo << ", " << r.d_hi << "]";
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
