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

#include "theory/ff/split_gb.h"

// external includes
#include <CoCoA/BigIntOps.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyRing.H>

// std includes
#include <variant>

// internal includes
#include "base/output.h"
#include "theory/ff/multi_roots.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

using PartialRoot = std::vector<std::optional<CoCoA::RingElem>>;
using Root = std::vector<CoCoA::RingElem>;

// fwd-declare helpers for clarity
namespace {
std::unique_ptr<AssignmentEnumerator> applyRule(const IncGb& ideal,
                                                const PartialRoot& partialRoot);

}  // namespace

SplitGb::SplitGb(std::vector<std::unique_ptr<IncGb>>&& bases) : d_bases(std::move(bases))
{
  AlwaysAssert(d_bases.size());
}

SplitGb::SplitGb(const SplitGb& other) : d_bases()
{
  for (const auto& b : other.d_bases)
  {
    d_bases.push_back(b->copy());
  }
}

bool SplitGb::trivial() const
{
  return std::any_of(d_bases.begin(), d_bases.end(), [](const auto& b) {
    return b->trivial();
  });
}

std::vector<CoCoA::RingElem> SplitGb::gens() const
{
  std::vector<CoCoA::RingElem> out;
  for (const auto& b : d_bases)
  {
    out.insert(out.end(), b->basis().begin(), b->basis().end());
  }
  return out;
}

const CoCoA::ring& SplitGb::polyRing() const { return d_bases[0]->polyRing(); }

bool SplitGb::containedIn(const CoCoA::RingElem& poly, size_t basisIdx) const
{
  return d_bases[basisIdx]->contains(poly);
}

size_t SplitGb::numBases() const { return d_bases.size(); }

const IncGb& SplitGb::operator[](size_t basisIdx) const
{
  return *d_bases[basisIdx];
}

IncGb& SplitGb::operator[](size_t basisIdx) { return *d_bases[basisIdx]; }

void SplitGb::addPoly(const CoCoA::RingElem& poly)
{
  for (auto& b : d_bases)
  {
    b->add(poly);
  }
}

void SplitGb::computeBasis()
{
  for (auto& b : d_bases)
  {
    b->computeBasis();
  }
}

namespace {

std::unique_ptr<AssignmentEnumerator> applyRule(const IncGb& ideal,
                                                const PartialRoot& r)
{
  Assert(static_cast<long>(r.size()) == CoCoA::NumIndets(ideal.polyRing()));
  Assert(std::any_of(
      r.begin(), r.end(), [](const auto& v) { return !v.has_value(); }));
  // (1) are the any polynomials that are univariate in an unassigned variable?
  const auto& gens = ideal.basis();
  for (const auto& p : gens)
  {
    int varNumber = CoCoA::UnivariateIndetIndex(p);
    if (varNumber >= 0 && !r[varNumber].has_value())
    {
      return factorEnumerator(p);
    }
  }
  // (2) if dimension 0, then compute such a polynomial
  if (ideal.zeroDimensional())
  {
    // If zero-dimensional, we compute a minimal polynomial in some unset
    // variable.
    for (size_t i = 0; i < r.size(); ++i)
    {
      if (!r[i].has_value())
      {
        CoCoA::RingElem minPoly = ideal.minimalPolynomial(i);
        return factorEnumerator(minPoly);
      }
    }
    Unreachable() << "There should be some unset var";
  }
  else
  {
    // If positive dimension, we make a list of unset variables and
    // round-robin guess.
    //
    // TODO(aozdemir): better model construction (cvc5-wishues/issues/138)
    std::vector<CoCoA::RingElem> toGuess{};
    for (size_t i = 0; i < r.size(); ++i)
    {
      if (!r[i].has_value())
      {
        toGuess.push_back(CoCoA::indet(ideal.polyRing(), i));
      }
    }
    return std::make_unique<RoundRobinEnumerator>(
        toGuess, ideal.polyRing()->myBaseRing());
  }
  Unreachable();
  return nullptr;
}

}  // namespace

// // returns one of {model, conflict, void (UNSAT w/o conflict)}.
// std::variant<std::vector<CoCoA::RingElem>, CoCoA::RingElem, bool>
// splitModelExtend(const SplitGb& origBases)
// {
//   // a frame: (basis, partial model, enumerator, processed)
//   using Frame = std::
//       tuple<SplitGb, PartialRoot, std::unique_ptr<AssignmentEnumerator>,
//       bool>;
//   PartialRoot emptyAssignment(CoCoA::NumIndets(origBases[0].polyRing()));
//   std::vector<Frame> stack = {{origBases, emptyAssignment, nullptr, false}};
//   while (stack.size())
//   {
//     const auto& [bases, r, enumerator, processed] = stack.back();
//     if (processed)
//     {
//     }
//     else
//     {
//       if (bases.trivial())
//       {
//         for (const auto& gen : bases.gens())
//         {
//           auto value = cocoaEval(gen, r);
//           if (value.has_value() && !CoCoA::IsZero(*value) &&
//           !bases[0].contains(gen))
//           {
//             return gen;
//           }
//         }
//       }
//     }
//   }
//   return false;
// }

// TODO: non-recursive (see above)
std::variant<std::vector<CoCoA::RingElem>, CoCoA::RingElem, bool>
splitModelExtend(const SplitGb& origBases,
                 const SplitGb& bases,
                 const PartialRoot& r)
{
  long nAssigned = std::count_if(
      r.begin(), r.end(), [](const auto& v) { return v.has_value(); });
  if (bases.trivial())
  {
    for (const auto& gen : origBases.gens())
    {
      auto value = cocoaEval(gen, r);
      if (value.has_value() && !CoCoA::IsZero(*value)
          && !origBases[0].contains(gen))
      {
        return gen;
      }
    }
    return false;
  }
  if (nAssigned == CoCoA::NumIndets(origBases.polyRing()))
  {
    std::vector<CoCoA::RingElem> out;
    for (const auto& v : r)
    {
      out.push_back(*v);
    }
    return out;
  }
  auto brancher = applyRule(bases[0], r);
  for (auto next = brancher->next(); next.has_value(); next = brancher->next())
  {
    long var = CoCoA::UnivariateIndetIndex(*next);
    Assert(var >= 0);
    CoCoA::RingElem val = -CoCoA::ConstantCoeff(*next);
    Assert(!r[var].has_value());
    PartialRoot newR = r;
    newR[var] = {val};
    Trace("ff::split::mc::debug")
        << std::string(1 + nAssigned, ' ')
        << CoCoA::indet(bases.polyRing(), var) << " = " << val << std::endl;
    SplitGb newBases = bases;
    newBases.addPoly(*next);
    newBases.computeBasis();
    auto result = splitModelExtend(origBases, newBases, newR);
    if (!std::holds_alternative<bool>(result))
    {
      return result;
    }
  }
  return false;
}

std::optional<std::vector<CoCoA::RingElem>> splitModelConstruct(
    const SplitGb& origBases)
{
  Trace("ff::split::mc") << "start splitModelConstruct" << std::endl;
  if (TraceIsOn("ff::split::mc"))
  {
    for (const auto& basis : origBases)
    {
      Trace("ff::split::mc") << " basis " << basis->name() << std::endl;
      for (const auto& g : basis->basis())
      {
        Trace("ff::split::mc") << "  " << g << std::endl;
      }
    }
  }
  SplitGb bases = origBases;
  PartialRoot emptyAssignment(CoCoA::NumIndets(origBases[0].polyRing()));
  while (true)
  {
    auto result = splitModelExtend(bases, bases, emptyAssignment);
    switch (result.index())
    {
      case 0:
      {
        const auto& model = std::get<std::vector<CoCoA::RingElem>>(result);
        if (TraceIsOn("ff::split::mc"))
        {
          Trace("ff::split::mc") << "got model " << std::endl;
          for (size_t i = 0; i < model.size(); ++i)
          {
            Trace("ff::split::mc")
                << " " << CoCoA::indet(origBases.polyRing(), i) << " = "
                << model[i] << std::endl;
          }
        }
        // no-op if assertions are off
        checkModel(origBases, model);
        return {std::move(model)};
      }
      case 1:
      {
        CoCoA::RingElem newPoly = std::get<CoCoA::RingElem>(result);
        Trace("ff::split::mc") << "conflict " << newPoly << std::endl;
        Assert(!bases[0].contains(newPoly));
        bases[0].add(newPoly);
        bases[0].computeBasis();
        break;
      }
      case 2:
      {
        Trace("ff::split::mc") << "unsat" << std::endl;
        return {};
      }
      default: Unreachable();
    }
  }
  Unreachable();
}

std::optional<CoCoA::RingElem> cocoaEval(CoCoA::RingElem poly,
                                         const PartialRoot& inputs)
{
  CoCoA::ring coeffs = CoCoA::CoeffRing(CoCoA::owner(poly));
  CoCoA::RingElem out = CoCoA::zero(coeffs);
  for (auto it = CoCoA::BeginIter(poly), end = CoCoA::EndIter(poly); it != end;
       ++it)
  {
    CoCoA::RingElem term = CoCoA::coeff(it);
    std::vector<CoCoA::BigInt> exponents;
    CoCoA::BigExponents(exponents, CoCoA::PP(it));
    for (size_t i = 0; i < exponents.size(); ++i)
    {
      if (!CoCoA::IsZero(exponents[i]))
      {
        if (!inputs[i].has_value())
        {
          return {};
        }
        term *= CoCoA::power(*inputs[i], exponents[i]);
      }
    }
    out += term;
  }
  return {out};
}

CoCoA::RingElem cocoaEval(CoCoA::RingElem poly, const Root& inputs)
{
  CoCoA::ring coeffs = CoCoA::CoeffRing(CoCoA::owner(poly));
  CoCoA::RingElem out = CoCoA::zero(coeffs);
  for (auto it = CoCoA::BeginIter(poly), end = CoCoA::EndIter(poly); it != end;
       ++it)
  {
    CoCoA::RingElem term = CoCoA::coeff(it);
    std::vector<CoCoA::BigInt> exponents;
    CoCoA::BigExponents(exponents, CoCoA::PP(it));
    for (size_t i = 0; i < exponents.size(); ++i)
    {
      if (!CoCoA::IsZero(exponents[i]))
      {
        term *= CoCoA::power(inputs[i], exponents[i]);
      }
    }
    out += term;
  }
  return out;
}

void checkModel(const SplitGb& origBases,
                const std::vector<CoCoA::RingElem>& model)
{
#ifdef CVC5_ASSERTIONS
  for (const auto& gen : origBases.gens())
  {
    auto value = cocoaEval(gen, model);
    if (!CoCoA::IsZero(value))
    {
      std::stringstream o;
      o << "Bad model!" << std::endl
        << "Generator " << gen << std::endl
        << "evaluated to " << value << std::endl
        << "under model: " << std::endl;
      for (size_t i = 0; i < model.size(); ++i)
      {
        o << " " << CoCoA::indet(origBases.polyRing(), i) << " -> " << model[i]
          << std::endl;
      }
      Assert(CoCoA::IsZero(value)) << o.str();
    }
  }
#endif  // CVC5_ASSERTIONS
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
