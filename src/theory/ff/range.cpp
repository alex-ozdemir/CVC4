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
#include <z3.h>

// std includes
#include <algorithm>
#include <numeric>
#include <unordered_map>

// internal includes
#include "context/cdhashmap.h"
#include "expr/node_traversal.h"
#include "expr/skolem_manager.h"
#include "options/ff_options.h"
#include "smt/env.h"
#include "smt/env_obj.h"
#include "theory/ff/gauss.h"
#include "theory/ff/parse.h"
#include "util/cse.h"
#include "util/finite_field_value.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

RangeSolver::RangeSolver(Env& env, const Integer& p) : EnvObj(env), FieldObj(p)
{
  Trace("ffr") << "new range solver; field:\n(define-sort F () (_ FiniteField "
               << size() << "))" << std::endl;
};

void RangeSolver::assertFact(TNode fact)
{
  Trace("ffr::fact") << "fact " << fact << std::endl;
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
    Trace("ffr::bounds") << "range " << var << ": " << r << std::endl;
    return;
  }

  // is this a range-shrinking disequality?
  if (options().ff.ffrNeTighten)
  {
    std::optional<std::pair<Node, FiniteFieldValue>> varNeValue =
        parse::varNeValue(fact);
    if (varNeValue.has_value())
    {
      auto it = d_assertedRanges.find(varNeValue->first);
      if (it != d_assertedRanges.end())
      {
        if (it->second.d_lo == varNeValue->second.toSignedInteger())
        {
          it->second.d_lo += 1;
          Trace("ffr::bounds") << "tighten to range " << varNeValue->first
                               << ": " << it->second << std::endl;
          return;
        }
        if (it->second.d_hi == varNeValue->second.toSignedInteger())
        {
          it->second.d_hi -= 1;
          Trace("ffr::bounds") << "tighten to range " << varNeValue->first
                               << ": " << it->second << std::endl;
          return;
        }
      }
    }
  }

  d_facts.emplace_back(fact);
}

z3::expr z3Range(const z3::expr& val, const Range& range)
{
  z3::expr lo = val.ctx().int_val(range.d_lo.toString().c_str());
  z3::expr hi = val.ctx().int_val(range.d_hi.toString().c_str());
  return (lo <= val) && (val <= hi);
}

bool isFf(TNode n)
{
  if (n.getType().isFiniteField()) return true;
  if (n.getKind() == Kind::OR)
  {
    for (const auto& c : n)
    {
      if (!isFf(c))
      {
        return false;
      }
    }
    return true;
  }
  else if (n.getKind() == Kind::EQUAL)
  {
    return n[0].getType().isFiniteField();
  }
  else if (n.getKind() == Kind::NOT)
  {
    return n[0].getKind() == Kind::EQUAL && n[0][0].getType().isFiniteField();
  }
  return false;
}

std::pair<Result, std::unordered_map<Node, FiniteFieldValue>>
RangeSolver::check()
{
  if (options().ff.ffrIntTimeout != 1)
  {
    auto resultAndModel = checkHelper(true, options().ff.ffrIntTimeout);
    if (resultAndModel.first == Result::SAT)
    {
      return resultAndModel;
    }
    if (resultAndModel.first == Result::UNSAT)
    {
      Trace("ffr") << "integer UNSAT " << std::endl;
    }
  }
  return checkHelper(false, 0);
}

std::pair<Result, std::unordered_map<Node, FiniteFieldValue>>
RangeSolver::checkHelper(bool unsound, size_t timeoutMs)
{
  Range bitRange = Range(0, 1);

  std::vector<Node> facts = d_facts;
  Node andFacts = NodeManager::currentNM()->mkAnd(facts);
  if (options().ff.ffrCse)
  {
    Node result = util::greedyCse(andFacts, Kind::FINITE_FIELD_ADD);
    Assert(result.getNumChildren() == andFacts.getNumChildren());
    Assert(rewrite(result) == andFacts);

    facts.clear();
    if (result.getKind() == Kind::AND)
    {
      facts.insert(facts.begin(), result.begin(), result.end());
    }
    else
    {
      facts.push_back(result);
    }
    andFacts = result;

    if (TraceIsOn("ffr") && d_facts.size() == facts.size())
    {
      for (size_t i = 0; i < facts.size(); ++i)
      {
        if (facts[i] != d_facts[i])
        {
          Trace("ffr") << "CSE " << d_facts[i] << std::endl
                       << " to " << facts[i] << std::endl;
        }
      }
    }
  }

  // map: bit var -> (acc var, bit number)
  std::unordered_map<Node, std::pair<Node, size_t>> varsToBits{};

  // extract bit-sums from facts
  if (options().ff.ffrElimBits)
  {
    size_t accI = 0;
    auto nm = NodeManager::currentNM();
    auto ffSort = nm->mkFiniteFieldType(size());
    std::unordered_map<Node, Node> rws{};

    // enumerate (parent, child) pairs; compute parent counts
    std::unordered_map<Node, size_t> parentCounts{};
    for (TNode parent : NodeDfsIterable(andFacts))
    {
      for (const Node& child : parent)
      {
        ++parentCounts.at(child);
      }
      parentCounts.insert({parent, 0});
    }

    // rewrite facts
    for (auto& f : facts)
    {
      for (TNode current :
           NodeDfsIterable(f, VisitOrder::POSTORDER, [&rws](TNode nn) {
             return rws.count(nn) || !isFf(nn);
           }))
      {
        if (current.isVar() || current.isConst())
        {
          rws.emplace(current, current);
          continue;
        }

        NodeBuilder builder(current.getKind());
        if (current.getMetaKind() == kind::MetaKind::PARAMETERIZED)
        {
          builder << current.getOperator();
        }
        for (const auto& c : current)
        {
          builder << (rws.count(c) ? TNode(rws.at(c)) : c);
        }
        Node newCurrent = builder.constructNode();

        if (newCurrent.getKind() == Kind::FINITE_FIELD_ADD)
        {
          // look for bit-sums in the addition; replace them with ranges.
          auto res = parse::bitSums(
              newCurrent,
              [this, &bitRange, &parentCounts](const Node& x) {
                size_t nParents = parentCounts.at(x);
                bool isBit = nParents == 1 && bitRange == getRange(x);
                Trace("ffr::isBit") << " isBit " << x << " : " << isBit << " ("
                                    << nParents << " parents)" << std::endl;
                return isBit;
              },
              [&parentCounts](const Node& x) {
                return !parentCounts.count(x) || parentCounts.at(x) >= 2;
              });
          if (res.has_value() && !res.value().first.empty())
          {
            auto& [bitSums, summands] = res.value();
            for (const auto& [coeff, bits] : bitSums)
            {
              std::string name = std::string("__acc") + std::to_string(accI);
              accI++;
              Node acc = nm->getSkolemManager()->mkDummySkolem(name, ffSort);
              d_assertedRanges.emplace(
                  acc, Range(0, Integer(2).pow(bits.size()) - 1));
              Node summand = coeff.isOne() ? acc
                                           : nm->mkNode(Kind::FINITE_FIELD_MULT,
                                                        nm->mkConst(coeff),
                                                        acc);
              summands.push_back(summand);
              if (TraceIsOn("ffr"))
              {
                Trace("ffr")
                    << "bitsum: " << acc << " = " << coeff << " * bitsum(";
                for (const auto& b : bits)
                {
                  Trace("ffr") << b << ",";
                }
                Trace("ffr") << ")" << std::endl;
              }
              for (size_t i = 0; i < bits.size(); ++i)
              {
                varsToBits.insert({bits[i], {acc, i}});
                d_assertedRanges.erase(bits[i]);
              }
            }
            if (summands.size() > 1)
            {
              newCurrent = nm->mkNode(Kind::FINITE_FIELD_ADD, summands);
            }
            else
            {
              Assert(summands.size() > 0);
              newCurrent = summands[0];
            }
          }
        }
        rws.insert({current, newCurrent});
      }
      f = rws.count(f) ? rws.at(f) : f;
    }
  }

  if (options().ff.ffrOr)
  {
    for (auto& f : facts)
    {
      const auto r = parse::zeroProduct(f);
      if (r.has_value())
      {
        const auto& [zero, product] = *r;
        bool rewrite = true;
        NodeBuilder orBuild(Kind::OR);
        for (const auto& t : product)
        {
          if (!getRange(t).floorDivideQuotient(size()).isZero())
          {
            rewrite = false;
            Trace("ffr::debug")
                << "no OR opt " << f << std::endl
                << "because " << t << "has q range "
                << getRange(t).floorDivideQuotient(size()) << std::endl;
            break;
          }
          orBuild << zero.eqNode(t);
        }
        if (rewrite)
        {
          Trace("ffr::debug") << "OR opt " << product << std::endl;
          f = orBuild.constructNode();
        }
      }
    }
  }

  std::unordered_map<Node, Node> gaussSubs{};
  std::unordered_set<Node> gaussVars{};
  // do gaussian elimination
  if (options().ff.ffrGauss)
  {
    auto nm = NodeManager::currentNM();
    std::unordered_set<Node> nodes{};
    std::unordered_set<Node> protVars{};
    std::unordered_set<Node> elimVars{};
    for (const auto& f : facts)
    {
      for (TNode current :
           NodeDfsIterable(f, VisitOrder::POSTORDER, [&nodes](TNode nn) {
             return nodes.count(nn) || !isFf(nn);
           }))
      {
        nodes.insert(current);
        if (current.isVar())
        {
          gaussVars.insert(current);
          if (d_assertedRanges.count(current))
          {
            protVars.insert(current);
          }
          else
          {
            elimVars.insert(current);
          }
        }
      }
    }
    std::unordered_map<Node, size_t> varToI{};
    std::vector<Node> iToVar{};
    for (const auto& var : elimVars)
    {
      varToI.emplace(var, iToVar.size());
      iToVar.push_back(var);
    }
    for (const auto& var : protVars)
    {
      varToI.emplace(var, iToVar.size());
      iToVar.push_back(var);
    }

    std::vector<
        std::pair<FiniteFieldValue, std::unordered_map<Node, FiniteFieldValue>>>
        affineFacts{};
    std::vector<Node> nonLinearFacts{};
    for (const auto& f : facts)
    {
      auto r = parse::affineEq(f);
      if (r.has_value())
      {
        Trace("ff::gauss::debug") << "affine fact " << f << std::endl;
        affineFacts.push_back(std::move(r.value()));
      }
      else
      {
        Trace("ff::gauss::debug") << "    nl fact " << f << std::endl;
        nonLinearFacts.push_back(f);
      }
    }
    size_t rows = affineFacts.size();
    // one extra protected column for the constant.
    iToVar.push_back(nm->mkConst(FiniteFieldValue(1, size())));
    size_t protCols = protVars.size() + 1;
    size_t cols = protCols + elimVars.size();
    size_t constCol = cols - 1;
    Trace("ff::gauss") << "Gauss starts with " << elimVars.size() << "/"
                       << (cols - 1) << " elim'ble vars and " << rows << " eqns"
                       << std::endl;
    Matrix matrix(size(), cols, protCols, rows);
    for (size_t r = 0; r < rows; ++r)
    {
      for (const auto& [var, coeff] : affineFacts[r].second)
      {
        size_t c = varToI.at(var);
        matrix.setEntry(r, c, coeff);
      }
      if (!affineFacts[r].first.isZero())
      {
        matrix.setEntry(r, constCol, affineFacts[r].first);
      }
    }
    Trace("ff::gauss::debug") << "before RREF" << std::endl << matrix;
    matrix.rref();
    Trace("ff::gauss::debug") << "after RREF" << std::endl << matrix;
    Assert(matrix.inRref());
    facts = std::move(nonLinearFacts);
    const auto& [substs, eqns] = matrix.output();
    Node zero = nm->mkConst(FiniteFieldValue(0, size()));
    for (const auto& [subVar, subExpr] : substs)
    {
      std::vector<Node> summands{};
      for (const auto& [col, coeff] : subExpr)
      {
        Node summand = col == constCol ? nm->mkConst(coeff)
                                       : nm->mkNode(Kind::FINITE_FIELD_MULT,
                                                    iToVar[col],
                                                    nm->mkConst(coeff));
        summands.push_back(summand);
      }
      Node var = iToVar[subVar];
      Node expr = mkAdd(std::move(summands));
      Trace("ff::gauss::debug") << " elim: " << var << "(" << subVar << ")"
                                << " to " << expr << std::endl;
      gaussSubs.insert({var, expr});
    }
    Trace("ff::gauss") << "Gauss ends; elim'd " << gaussSubs.size() << " vars"
                       << " of " << cols - 1 << " vars" << std::endl;
    for (const auto& eqn : eqns)
    {
      std::vector<Node> summands{};
      for (const auto& [col, coeff] : eqn)
      {
        summands.push_back(nm->mkNode(
            Kind::FINITE_FIELD_MULT, iToVar[col], nm->mkConst(coeff)));
      }
      facts.push_back(rewrite(zero.eqNode(mkAdd(std::move(summands)))));
      Trace("ff::gauss::debug")
          << "post-rref fact: " << facts.back() << std::endl;
    }
    Node factsAnd = nm->mkAnd(facts);
    Node factsAndSub = factsAnd.substitute(gaussSubs.begin(), gaussSubs.end());
    facts.clear();
    if (factsAnd.getKind() == Kind::AND)
    {
      Assert(factsAnd.getNumChildren() == factsAndSub.getNumChildren());
      for (const auto& c : factsAndSub)
      {
        Trace("ff::gauss::debug") << "post-gauss fact: " << c << std::endl;
        facts.push_back(c);
      }
    }
    else
    {
      Trace("ff::gauss::debug")
          << "post-gauss fact: " << factsAndSub << std::endl;
      facts.push_back(factsAndSub);
    }
  }

  // embed facts for z3
  z3::context ctx;
  // z3::set_param("verbose", 20);
  z3::expr zero = ctx.int_val(0);
  z3::expr one = ctx.int_val(1);
  z3::expr two = ctx.int_val(2);
  z3::expr p = ctx.int_val(size().d_val.toString().c_str());
  size_t fI = 0;
  std::unordered_map<Node, z3::expr> ints{};
  std::vector<z3::expr> assertions{};

  // every range must be asserted, regardless of use.
  for (const auto& [var, range] : d_assertedRanges)
  {
    z3::expr e = ctx.int_const(var.getName().c_str());
    assertions.push_back(z3Range(e, range));
    ints.insert({var, e});
  }

  for (const auto& f : facts)
  {
    Trace("ffr::debug") << "enc fact " << f << std::endl;
    for (TNode current :
         NodeDfsIterable(f, VisitOrder::POSTORDER, [&ints](TNode nn) {
           return ints.count(nn) || !isFf(nn);
         }))
    {
      Assert(!ints.count(current));
      z3::expr e = zero;
      if (current.isVar())
      {
        e = ctx.int_const(current.getName().c_str());
      }
      else if (current.isConst())
      {
        e = ctx.int_val(current.getConst<FiniteFieldValue>()
                            .toSignedInteger()
                            .toString()
                            .c_str());
      }
      else if (current.getKind() == Kind::FINITE_FIELD_ADD)
      {
        e = zero;
        for (const auto& child : current)
        {
          e = e + ints.at(child);
        }
      }
      else if (current.getKind() == Kind::FINITE_FIELD_BITSUM)
      {
        e = zero;
        z3::expr k = one;
        for (const auto& child : current)
        {
          e = e + k * ints.at(child);
          k = k * two;
        }
      }
      else if (current.getKind() == Kind::FINITE_FIELD_MULT)
      {
        e = ints.at(current[0]);
        for (size_t i = 1; i < current.getNumChildren(); ++i)
        {
          e = e * ints.at(current[i]);
        }
      }
      else if (current.getKind() == Kind::EQUAL
               || current.getKind() == Kind::NOT
               || current.getKind() == Kind::OR)
      {
        // pass
      }
      else
      {
        Unimplemented() << "Unsupported kind: " << current.getKind();
      }
      ints.insert({current, e});
    }

    if (f.getKind() == Kind::EQUAL)
    {
      if (unsound)
      {
        assertions.push_back(ints.at(f[0]) == ints.at(f[1]));
      }
      else if (options().ff.ffrMod)
      {
        assertions.push_back((ints.at(f[0]) - ints.at(f[1])) % p == 0);
      }
      else
      {
        // equality: left - right = q * p
        z3::expr q =
            ctx.int_const((std::string("__q") + std::to_string(fI)).c_str());
        fI++;
        assertions.push_back((ints.at(f[0]) - ints.at(f[1])) == q * p);

        if (options().ff.ffrBoundQuotient)
        {
          // use range analysis to bound q tightly.
          auto diffRange = getRange(f[0]) - getRange(f[1]);
          Trace("ffr::debug")
              << "l range " << f[0] << ": " << getRange(f[0]) << std::endl;
          Trace("ffr::debug")
              << "r range " << f[1] << ": " << getRange(f[1]) << std::endl;
          auto qRange = diffRange.floorDivideQuotient(size());
          Trace("ffr") << "for eq " << f << std::endl;
          Trace("ffr") << "q range " << qRange.d_lo << " to " << qRange.d_hi
                       << std::endl;
          assertions.push_back(z3Range(q, qRange));
        }
      }
    }
    else if (f.getKind() == Kind::OR)
    {
      // we already know all children are exact equalities
      z3::expr_vector eqs(ctx);
      for (const auto& c : f)
      {
        Assert(isFfZero(c[0]));
        Assert(getRange(c[1]).floorDivideQuotient(size()).isZero());
        eqs.push_back(ints.at(c[1]) == 0);
      }
      assertions.push_back(z3::mk_or(eqs));
    }
    else if (f.getKind() == Kind::CONST_BOOLEAN)
    {
      if (!f.getConst<bool>())
      {
        return {Result::UNKNOWN, {}};
      }
    }
    else
    {
      Assert(f.getKind() == Kind::NOT && f[0].getKind() == Kind::EQUAL) << f;
      Node e = f[0];
      z3::expr diff = ints.at(e[0]) - ints.at(e[1]);
      if (unsound)
      {
        assertions.push_back(diff != 0);
      }
      else if (options().ff.ffrMod)
      {
        assertions.push_back(diff % p != 0);
      }
      else
      {
        // inequality:
        if (options().ff.ffrNeNorm)
        {
          // encode with norm: diff - __n = __q * p
          //                   0 < __n < p
          //
          z3::expr q =
              ctx.int_const((std::string("__q") + std::to_string(fI)).c_str());
          z3::expr n =
              ctx.int_const((std::string("__n") + std::to_string(fI)).c_str());
          fI++;
          assertions.push_back(diff - n == q * p);
          assertions.push_back((zero < n) && (n < p));
          if (options().ff.ffrBoundQuotient)
          {
            // use range analysis to bound q tightly.
            auto diffRange = getRange(e[0]) - getRange(e[1]);
            Range nRange(1, size());
            auto qRange = diffRange.floorDivideQuotient(size());
            Trace("ffr") << "for diseq " << f << std::endl;
            Trace("ffr") << "q range " << qRange.d_lo << " to " << qRange.d_hi
                         << std::endl;
            assertions.push_back(z3Range(q, qRange));
          }
        }
        else
        {
          // encode with inverse: diff * __i = 1 + __q * p
          z3::expr q =
              ctx.int_const((std::string("__q") + std::to_string(fI)).c_str());
          z3::expr i =
              ctx.int_const((std::string("__i") + std::to_string(fI)).c_str());
          fI++;
          assertions.push_back(diff * i == one + q * p);
        }
      }

      // assertions.push_back((i >= zero) && (i < p));
    }
  }

  Trace("ffr::z3") << "z3 version: " << Z3_get_full_version() << std::endl;
  // specify tactic manually.
  z3::solver s = z3::tactic(ctx, "qfnia").mk_solver();
  if (timeoutMs != 0)
  {
    s.set(":timeout", static_cast<uint32_t>(timeoutMs));
  }
  if (TraceIsOn("ffr::z3"))
  {
    for (const auto& a : assertions)
    {
      Trace("ffr::z3") << "to z3: " << a << std::endl;
    }
  }
  z3::check_result r = s.check(assertions.size(), &assertions[0]);
  switch (r)
  {
    case z3::check_result::sat:
    {
      std::unordered_map<Node, FiniteFieldValue> model{};
      std::unordered_map<Node, Node> modelAsNodes{};
      auto z3model = s.get_model();
      for (size_t i = 0; i < z3model.num_consts(); ++i)
      {
        auto decl = z3model.get_const_decl(i);
        auto interp = z3model.get_const_interp(decl);
        Trace("ffr::z3") << "z3 model " << decl.name() << " = " << interp
                         << std::endl;
      }
      auto nm = NodeManager::currentNM();
      for (const auto& it : ints)
      {
        if (it.first.isVar() && !varsToBits.count(it.first))
        {
          // Not sure what to do with the argument to get_decimal_string.
          auto val = FiniteFieldValue(
              Integer(z3model.eval(ints.at(it.first)).get_decimal_string(0)),
              size());
          Trace("ffr::model") << "model " << it.first << ": "
                              << val.toSignedInteger() << std::endl;
          model.insert({it.first, val});
          modelAsNodes.insert({it.first, nm->mkConst(val)});
        }
      }
      FiniteFieldValue zeroFf(0, size());
      for (const auto& v : gaussVars)
      {
        if (!gaussSubs.count(v))
        {
          model.insert({v, zeroFf});
          modelAsNodes.insert({v, nm->mkConst(zeroFf)});
          Trace("ffr::model") << "model " << v << ": "
                              << model.at(v).toSignedInteger() << std::endl;
        }
      }
      for (const auto& [v, e] : gaussSubs)
      {
        Node k =
            rewrite(e.substitute(modelAsNodes.begin(), modelAsNodes.end()));
        Assert(k.isConst())
            << "non-const " << k << "\nfor " << v << " in model;\nfrom " << e;
        model.insert({v, k.getConst<FiniteFieldValue>()});
        modelAsNodes.insert({v, k});
        Trace("ffr::model") << "model " << v << ": "
                            << model.at(v).toSignedInteger() << std::endl;
      }
      for (const auto& [v, entry] : varsToBits)
      {
        const auto& [cvcVar, bitI] = entry;
        bool bit = model.at(cvcVar).toInteger().isBitSet(bitI);
        auto val = FiniteFieldValue(bit, size());
        Assert(!model.count(v));
        model.insert({v, val});
        modelAsNodes.insert({v, nm->mkConst(val)});
        Trace("ffr::model") << "model " << v << ": "
                            << model.at(v).toSignedInteger() << std::endl;
      }

      return {Result::SAT, std::move(model)};
    }
    case z3::check_result::unsat:
    {
      if (TraceIsOn("ffr::core"))
      {
        Trace("ffr::core") << "Core:" << std::endl;
        for (const auto& c : s.unsat_core())
        {
          Trace("ffr::core") << " " << c << std::endl;
        }
      }
      return {Result::UNSAT, {}};
    }
    case z3::check_result::unknown:
    {
      return {Result::UNKNOWN, {}};
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
      r = Range(current.getConst<FiniteFieldValue>().toSignedInteger());
    }
    else if (current.getKind() == Kind::FINITE_FIELD_ADD)
    {
      r = std::accumulate(
          current.begin(),
          current.end(),
          Range(0),
          [this](Range acc, TNode child) { return acc + d_ranges.at(child); });
    }
    else if (current.getKind() == Kind::FINITE_FIELD_BITSUM)
    {
      r = Range(0);
      for (size_t i = 0; i < current.getNumChildren(); ++i)
      {
        r = r + d_ranges.at(current[i]) * Integer(1).multiplyByPow2(i);
      }
    }
    else if (current.getKind() == Kind::FINITE_FIELD_MULT)
    {
      r = std::accumulate(
          current.begin(),
          current.end(),
          Range(1),
          [this](Range acc, TNode child) { return acc * d_ranges.at(child); });
    }
    else if (current.getKind() == Kind::FINITE_FIELD_NEG)
    {
      r = -d_ranges.at(current[0]);
    }
    else if (current.isVar() || current.getKind() == Kind::APPLY_UF)
    {
      r = Range(0, size().d_val - 1);
    }
    else
    {
      Unimplemented() << "Unsupported kind: " << current.getKind();
    }
    Trace("ffr::debug") << "range " << current << ": " << r << std::endl;
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

Range::Range(const Integer& singleton) : d_lo(singleton), d_hi(singleton){};

Range::Range(const Integer& lo, const Integer& hi) : d_lo(lo), d_hi(hi)
{
  if (d_hi < d_lo)
  {
    std::swap(d_hi, d_lo);
  }
};

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

Range Range::operator*(const Integer& other) const
{
  if (other >= 0)
  {
    return {d_hi * other, d_lo * other};
  }
  else
  {
    return {d_lo * other, d_hi * other};
  }
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

bool Range::isZero() const { return d_lo == 0 && d_hi == 0; }

Range Range::floorDivideQuotient(const Integer& q) const
{
  Assert(q.strictlyPositive());
  return Range(d_lo.floorDivideQuotient(q), d_hi.floorDivideQuotient(q));
}

std::ostream& operator<<(std::ostream& o, const Range& r)
{
  return o << "[" << r.d_lo << ", " << r.d_hi << "]";
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
