/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Kshitij Bansal
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A configurably incremental groebner basis engine.
 */

#include "theory/ff/groebner.h"

#include <CoCoA/BigInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/ring.H>

#include <numeric>

#include "expr/node_manager_attributes.h"
#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "smt/env_obj.h"
#include "theory/ff/model.h"
#include "theory/ff/toy_gb.h"
#include "theory/ff/toy_gb_blame.h"
#include "util/finite_field.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

IncrementalIdeal::IncrementalIdeal(Env& env, CoCoA::ring polyRing)
    : EnvObj(env),
      d_context(std::make_unique<context::Context>()),
      d_gens(d_context.get()),
      d_basis(d_context.get()),
      d_hasCore(d_context.get()),
      d_core(d_context.get()),
      d_hasSolution(d_context.get()),
      d_solution(d_context.get())
{
}

void IncrementalIdeal::pushGenerators(std::vector<CoCoA::RingElem>&& gens)
{
  d_context->push();
  d_tracer.push();
  std::vector<CoCoA::RingElem> theseGens = d_basis.get();
  for (auto& g : gens)
  {
    d_gens.emplace_back(std::move(g));
    d_tracer.addInput(d_gens.back());
    theseGens.push_back(d_gens.back());
  }
  d_tracer.setFunctionPointers();
  if (TraceIsOn("ff::groebner::push"))
  {
    for (const auto& b : theseGens)
    {
      Trace("ff::groebner::push") << "gens: " << b << std::endl;
    }
  }
  CoCoA::ideal ideal = CoCoA::ideal(theseGens);
  d_basis = CoCoA::GBasis(ideal);
  if (TraceIsOn("ff::groebner::push"))
  {
    for (const auto& b : d_basis.get())
    {
      Trace("ff::groebner::push") << "basis: " << b << std::endl;
    }
  }
  d_hasCore.set(false);
  d_hasSolution.set({});
}

bool IncrementalIdeal::idealIsTrivial()
{
  return d_basis.get().size() == 1 && CoCoA::deg(d_basis.get().front()) == 0;
}

const std::vector<size_t>& IncrementalIdeal::trivialCoreIndices()
{
  Assert(idealIsTrivial());
  if (!d_hasCore.get())
  {
    d_core = d_tracer.trace(d_basis.get().front());
    d_hasCore.set(true);
  }
  return d_core.get();
}

std::vector<CoCoA::RingElem> IncrementalIdeal::trivialCore()
{
  std::vector<CoCoA::RingElem> r;
  for (size_t i : trivialCoreIndices())
  {
    r.push_back(d_gens[i]);
  }
  return r;
}

bool IncrementalIdeal::hasSolution()
{
  if (idealIsTrivial())
  {
    return false;
  }
  else
  {
    ensureSolution();
  }
  return d_hasSolution.get().value();
}

void IncrementalIdeal::ensureSolution()
{
  if (!d_hasSolution.get().has_value())
  {
    std::vector<CoCoA::RingElem> root = commonRoot(CoCoA::ideal(d_basis.get()));
    if (root.empty())
    {
      d_hasSolution.set({false});
    }
    else
    {
      d_hasSolution.set({true});
      d_solution.set(root);
    }
  }
}

const std::vector<CoCoA::RingElem>& IncrementalIdeal::solution()
{
  ensureSolution();
  return d_solution.get();
}

void IncrementalIdeal::pop()
{
  d_context->pop();
  d_tracer.pop();
}

SubTheory::SubTheory(Env& env, Incrementality i, Integer modulus)
    : EnvObj(env),
      context::ContextNotifyObj(context()),
      d_facts(context()),
      d_checkIndices(context()),
      d_inc(i),
      d_baseRing(CoCoA::NewZZmod(CoCoA::BigIntFromString(modulus.toString()))),
      d_modulus(modulus)
{
  AlwaysAssert(modulus.isProbablePrime()) << "non-prime fields are unsupported";
}

void SubTheory::preRegisterTerm(TNode n)
{
  Assert(!d_polyRing.has_value());
  if (n.isVar())
  {
    d_vars.insert(n);
  }
  else if (n.getKind() == Kind::EQUAL)
  {
    d_atoms.insert(n);
  }
}

// CoCoA symbols must start with a letter and contain only letters and
// underscores.
//
// Thus, our encoding is: v_ESCAPED where any underscore or invalid character
// in NAME is replace in ESCAPED with an underscore followed by a base-16
// encoding of its ASCII code using alphabet abcde fghij klmno p, followed by
// another _.
//
// Sorry. It sucks, but we don't have much to work with here...
std::string varNameToSymName(const std::string& varName)
{
  std::ostringstream o;
  o << "v_";
  for (const auto c : varName)
  {
    if (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z'))
    {
      o << c;
    }
    else
    {
      uint8_t code = c;
      o << "_"
        << "abcdefghijklmnop"[code & 0x0f]
        << "abcdefghijklmnop"[(code >> 4) & 0x0f] << "_";
    }
  }
  return o.str();
}

void SubTheory::ensureInitPolyRing()
{
  if (!d_polyRing.has_value())
  {
    std::vector<CoCoA::symbol> symbols;
    for (const auto& v : d_vars)
    {
      symbols.push_back(
          CoCoA::symbol(varNameToSymName(v.getAttribute(expr::VarNameAttr()))));
    }
    for (size_t i = 0; i < d_atoms.size(); ++i)
    {
      symbols.push_back(CoCoA::symbol("i", i));
    }
    d_polyRing = CoCoA::NewPolyRing(d_baseRing, symbols);
    size_t i = 0;
    for (const auto& v : d_vars)
    {
      d_translationCache.insert({v, CoCoA::indet(d_polyRing.value(), i)});
      d_symbolIdxVars.insert({i, v});
      ++i;
    }
    for (const auto& a : d_atoms)
    {
      d_atomInverses.insert({a, CoCoA::indet(d_polyRing.value(), i)});
      Trace("ff::inverses") << "inverse for " << a << std::endl;
      ++i;
    }
    Assert(!d_incrementalIdeal.has_value());
    d_incrementalIdeal.emplace(d_env, d_polyRing.value());
    d_updateIndices.push_back(0);
  }
}

void SubTheory::notifyFact(TNode fact)
{
  ensureInitPolyRing();
  d_facts.emplace_back(fact);
  d_model.clear();
}

void SubTheory::postCheck(Theory::Effort e)
{
  d_checkIndices.push_back(d_facts.size());
  if (e == Theory::EFFORT_STANDARD)
  {
    if (d_inc == Incrementality::Eager)
    {
      computeBasis(d_facts.size());
    }
  }
  else if (e == Theory::EFFORT_FULL)
  {
    if (d_inc == Incrementality::Eager || d_inc == Incrementality::Lazy)
    {
      for (size_t i : d_checkIndices)
      {
        if (i > d_updateIndices.back())
        {
          computeBasis(i);
          if (inConflict()) return;
        }
      }
    }
    else
    {
      computeBasis(d_facts.size());
    }
    extractModel();
  }
}

bool SubTheory::inConflict() const { return !d_conflict.empty(); }

const std::vector<Node>& SubTheory::conflict() const { return d_conflict; }

const std::unordered_map<Node, Node>& SubTheory::model() const
{
  return d_model;
}

void SubTheory::contextNotifyPop()
{
  while (d_updateIndices.back() > d_facts.size())
  {
    d_updateIndices.pop_back();
    d_incrementalIdeal.value().pop();
    d_conflict.clear();
  }
}

void SubTheory::computeBasis(size_t factIndex)
{
  Assert(d_conflict.empty());
  Assert(d_updateIndices.size() > 0);
  Assert(factIndex > d_updateIndices.back());
  IncrementalIdeal& ideal = d_incrementalIdeal.value();
  std::vector<CoCoA::RingElem> newGens;
  for (size_t i = d_updateIndices.back(); i < factIndex; ++i)
  {
    TNode fact = d_facts[i];
    translate(fact);
    newGens.push_back(d_translationCache.at(fact));
  }
  ideal.pushGenerators(std::move(newGens));
  d_updateIndices.push_back(factIndex);
  if (ideal.idealIsTrivial())
  {
    for (size_t i : ideal.trivialCoreIndices())
    {
      d_conflict.push_back(d_facts[i]);
    }
  }
}

void SubTheory::extractModel()
{
  IncrementalIdeal& ideal = d_incrementalIdeal.value();
  Trace("ff::check::model") << "constructing model" << std::endl;
  d_model.clear();
  if (ideal.hasSolution())
  {
    Trace("ff::check::model") << "found model" << std::endl;
    const auto& values = ideal.solution();
    NodeManager* nm = NodeManager::currentNM();
    for (size_t i = 0, numVars = d_vars.size(); i < numVars; ++i)
    {
      std::ostringstream symName;
      symName << CoCoA::indet(d_polyRing.value(), i);
      Node var = d_symbolIdxVars.at(i);
      std::ostringstream valStr;
      valStr << values[i];
      Integer integer(valStr.str(), 10);
      FiniteField literal(integer, d_modulus);
      Node value = nm->mkConst(literal);

      Trace("ff::check::model") << var << ": " << value << std::endl;
      d_model.emplace(var, value);
    }
  }
  else
  {
    d_conflict.insert(d_conflict.begin(), d_facts.begin(), d_facts.end());
  }
}

void SubTheory::translate(TNode t)
{
  auto& cache = d_translationCache;
  // Build polynomials for terms
  for (const auto& node :
       NodeDfsIterable(t, VisitOrder::POSTORDER, [&cache](TNode nn) {
         return cache.count(nn) > 0;
       }))
  {
    if (node.getType().isFiniteField() || node.getKind() == Kind::EQUAL
        || node.getKind() == Kind::NOT)
    {
      CoCoA::RingElem poly;
      std::vector<CoCoA::RingElem> subPolys;
      std::transform(node.begin(),
                     node.end(),
                     std::back_inserter(subPolys),
                     [&cache](Node n) { return cache[n]; });
      switch (node.getKind())
      {
        // FF-term cases:
        case Kind::FINITE_FIELD_ADD:
          poly = std::accumulate(
              subPolys.begin(),
              subPolys.end(),
              CoCoA::RingElem(d_polyRing.value()->myZero()),
              [](CoCoA::RingElem a, CoCoA::RingElem b) { return a + b; });
          break;
        case Kind::FINITE_FIELD_NEG: poly = -subPolys[0]; break;
        case Kind::FINITE_FIELD_MULT:
          poly = std::accumulate(
              subPolys.begin(),
              subPolys.end(),
              CoCoA::RingElem(d_polyRing.value()->myOne()),
              [](CoCoA::RingElem a, CoCoA::RingElem b) { return a * b; });
          break;
        case Kind::CONST_FINITE_FIELD:
          poly = d_polyRing.value()->myOne()
                 * CoCoA::BigIntFromString(
                     node.getConst<FiniteField>().getValue().toString());
          break;
        // fact cases:
        case Kind::EQUAL: poly = subPolys[0] - subPolys[1]; break;
        case Kind::NOT:
          Assert(node[0].getKind() == Kind::EQUAL);
          poly = subPolys[0] * d_atomInverses.at(node[0]) - 1;
          break;
        default:
          Unreachable() << "Invalid finite field kind: " << node.getKind();
      }
      Trace("ff::check::trans")
          << "Translated " << node << "\t-> " << poly << std::endl;
      cache.insert(std::make_pair(node, poly));
    }
  }
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
