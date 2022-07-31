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
 * Finite fields model construction
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/model.h"

#include <CoCoA/BigIntOps.H>
#include <CoCoA/RingFp.H>
#include <CoCoA/SparsePolyOps-MinPoly.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/factor.H>
#include <CoCoA/factorization.H>

#include <algorithm>
#include <memory>
#include <sstream>

#include "smt/assertions.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

AssignmentEnumerator::~AssignmentEnumerator(){};

ListEnumerator::ListEnumerator(const std::vector<CoCoA::RingElem>&& options)
    : d_remainingOptions(std::move(options))
{
  std::reverse(d_remainingOptions.begin(), d_remainingOptions.end());
}

ListEnumerator::~ListEnumerator(){};

std::optional<CoCoA::RingElem> ListEnumerator::next()
{
  if (d_remainingOptions.empty())
  {
    return {};
  }
  else
  {
    CoCoA::RingElem v = d_remainingOptions.back();
    d_remainingOptions.pop_back();
    return v;
  }
}

std::unique_ptr<ListEnumerator> factorEnumerator(CoCoA::RingElem univariatePoly)
{
  Assert(CoCoA::UnivariateIndetIndex(univariatePoly) >= 0);
  const auto factors = CoCoA::factor(univariatePoly);
  std::vector<CoCoA::RingElem> options{};
  for (const auto& factor : factors.myFactors())
  {
    if (CoCoA::deg(factor) == 1)
    {
      Assert(CoCoA::IsOne(CoCoA::LC(factor)));
      options.push_back(factor);
    }
  }
  return std::make_unique<ListEnumerator>(std::move(options));
}

RoundRobinEnumerator::RoundRobinEnumerator(
    const std::vector<CoCoA::RingElem>& vars, const CoCoA::ring& ring)
    : d_vars(vars),
      d_ring(ring),
      d_idx(),
      d_maxIdx(
          CoCoA::power(CoCoA::characteristic(ring), CoCoA::LogCardinality(ring))
          * vars.size())
{
}

RoundRobinEnumerator::~RoundRobinEnumerator() {}

std::optional<CoCoA::RingElem> RoundRobinEnumerator::next()
{
  std::optional<CoCoA::RingElem> ret{};
  if (d_idx != d_maxIdx)
  {
    size_t whichVar = d_idx % d_vars.size();
    CoCoA::BigInt whichVal = d_idx / d_vars.size();
    CoCoA::RingElem val = d_ring->myZero();
    val += whichVal;
    ret = d_vars[whichVar] - val;
    ++d_idx;
  }
  return ret;
}

bool isUnsat(const CoCoA::ideal& ideal)
{
  const auto& gens = CoCoA::GBasis(ideal);
  return !(gens.size() > 1 || CoCoA::deg(gens[0]) > 0);
}

template <typename T>
std::string ostring(const T& t)
{
  std::ostringstream o;
  o << t;
  return o.str();
}

std::pair<size_t, CoCoA::RingElem> extractAssignment(
    const CoCoA::RingElem& elem)
{
  Assert(CoCoA::deg(elem) == 1);
  Assert(CoCoA::NumTerms(elem) <= 2);
  CoCoA::RingElem m = CoCoA::monic(elem);
  int varNumber = CoCoA::UnivariateIndetIndex(elem);
  Assert(varNumber >= 0);
  return {varNumber, -CoCoA::ConstantCoeff(m)};
}

std::unordered_set<std::string> assignedVars(const CoCoA::ideal& ideal)
{
  std::unordered_set<std::string> ret{};
  for (const auto& g : CoCoA::GBasis(ideal))
  {
    if (CoCoA::deg(g) == 1)
    {
      int varNumber = CoCoA::UnivariateIndetIndex(g);
      if (varNumber >= 0)
      {
        ret.insert(ostring(CoCoA::indet(ideal->myRing(), varNumber)));
      }
    }
  }
  return ret;
}

bool allVarsAssigned(const CoCoA::ideal& ideal)
{
  return assignedVars(ideal).size()
         == (size_t)CoCoA::NumIndets(ideal->myRing());
}

std::unique_ptr<AssignmentEnumerator> brancher(const CoCoA::ideal& ideal)
{
  CoCoA::ring polyRing = ideal->myRing();
  Assert(!isUnsat(ideal));
  // first, we look for super-linear univariate polynomials.
  const auto& gens = CoCoA::GBasis(ideal);
  for (const auto& p : gens)
  {
    int varNumber = CoCoA::UnivariateIndetIndex(p);
    if (varNumber >= 0 && CoCoA::deg(p) > 1)
    {
      return factorEnumerator(p);
    }
  }
  // now, we check the dimension
  if (CoCoA::IsZeroDim(ideal))
  {
    // If zero-dimensional, we compute a minimal polynomial in some unset
    // variable.
    std::unordered_set<std::string> alreadySet = assignedVars(ideal);
    for (const auto& var : CoCoA::indets(polyRing))
    {
      std::string varName = ostring(var);
      if (!alreadySet.count(ostring(var)))
      {
        CoCoA::RingElem minPoly = CoCoA::MinPolyQuot(var, ideal, var);
        return factorEnumerator(minPoly);
      }
    }
    Unreachable()
        << "There should be no unset variables in zero-dimensional ideal";
  }
  else
  {
    // If positive dimensional, we make a list of unset variables and
    // round-robin guess.
    //
    // TODO(aozdemir): guess free variables first!
    std::unordered_set<std::string> alreadySet = assignedVars(ideal);
    std::vector<CoCoA::RingElem> toGuess{};
    for (const auto& var : CoCoA::indets(polyRing))
    {
      std::string varName = ostring(var);
      if (!alreadySet.count(ostring(var)))
      {
        toGuess.push_back(var);
      }
    }
    return std::make_unique<RoundRobinEnumerator>(toGuess,
                                                  polyRing->myBaseRing());
  }
}

std::vector<CoCoA::RingElem> commonRoot(const CoCoA::ideal& initialIdeal)
{
  CoCoA::ring polyRing = initialIdeal->myRing();
  // We maintain two stacks:
  // * one of ideal
  // * one of branch points
  //
  std::vector<CoCoA::ideal> ideals{initialIdeal};
  std::vector<std::unique_ptr<AssignmentEnumerator>> branchers{};
  while (!ideals.empty())
  {
    const auto& ideal = ideals.back();
    // If the ideal is UNSAT, drop it.
    if (isUnsat(ideal))
    {
      ideals.pop_back();
    }
    // If the ideal has a linear polynomial in each variable, we've found a
    // value.
    else if (allVarsAssigned(ideal))
    {
      std::unordered_map<size_t, CoCoA::RingElem> varNumToValue{};
      const auto& gens = CoCoA::GBasis(ideal);
      size_t numIndets = CoCoA::NumIndets(polyRing);
      Assert(gens.size() == numIndets);
      for (const auto& g : gens)
      {
        varNumToValue.insert(extractAssignment(g));
      }
      std::vector<CoCoA::RingElem> values{};
      for (size_t i = 0; i < numIndets; ++i)
      {
        values.push_back(varNumToValue[i]);
      }
      return values;
    }
    // If there are more ideals than branchers, branch
    else if (ideals.size() > branchers.size())
    {
      Assert(ideals.size() == branchers.size() + 1);
      branchers.push_back(brancher(ideal));
    }
    // Otherwise, this ideal should have a brancher; get the next branch
    else
    {
      Assert(ideals.size() == branchers.size());
      std::optional<CoCoA::RingElem> choicePoly = branchers.back()->next();
      // construct a new ideal from the branch
      if (choicePoly.has_value())
      {
        std::vector<CoCoA::RingElem> newGens = CoCoA::GBasis(ideal);
        newGens.push_back(choicePoly.value());
        ideals.push_back(CoCoA::ideal(newGens));
      }
      // or drop this ideal if we're out of branches.
      else
      {
        branchers.pop_back();
        ideals.pop_back();
      }
    }
  }
  // Could not find any solution; return empty.
  return {};
}

// Sage common root.
std::vector<CoCoA::RingElem> commonRootSage(const CoCoA::ideal& ideal)
{
  CoCoA::ring polyRing = ideal->myRing();
  CoCoA::ring ring = ideal->myRing()->myBaseRing();
  CoCoA::BigInt size =
      CoCoA::power(CoCoA::characteristic(ring), CoCoA::LogCardinality(ring));
  // Write the root-finding problem to a temporary file.
  std::string problemPath = "cvc5-ff-problem-XXXXXX";
  std::unique_ptr<std::fstream> problemFile = openTmpFile(&problemPath);
  *problemFile << "size: " << size << std::endl;
  *problemFile << "variables:";
  for (const auto& symbol : CoCoA::indets(polyRing))
  {
    *problemFile << " " << symbol;
  }
  *problemFile << std::endl;
  // use the g-basis that we already have.
  for (const auto& basisPoly : CoCoA::GBasis(ideal))
  {
    *problemFile << "polynomial: " << basisPoly << std::endl;
  }
  problemFile->flush();

  // create a temporary file for the solution.
  std::string solutionPath = "cvc5-ff-solution-XXXXXX";
  std::unique_ptr<std::fstream> solutionFile = openTmpFile(&solutionPath);

  // run the script
  std::ostringstream cmdBuilder;
  cmdBuilder << FF_MODEL_SCRIPT_PATH << " -i " << problemPath << " -o "
             << solutionPath;
  std::string cmd = cmdBuilder.str();
  int retValue = std::system(cmd.c_str());
  Assert(retValue == 0) << "Non-zero return code from model script";

  // parse the output
  std::unordered_map<std::string, std::string> solutionStrs;
  while (true)
  {
    std::string var;
    std::string val;
    *solutionFile >> var >> val;
    if (solutionFile->eof())
    {
      break;
    }
    Assert(solutionFile->good())
        << "IO error in reading solution file" << std::strerror(errno);
    Trace("ff::check::model") << var << ": " << val << std::endl;
    solutionStrs.emplace(var, val);
  }

  // The output is non-empty if there are non-extension ("real") roots.
  if (!solutionStrs.size())
  {
    return {};
  }

  std::vector<CoCoA::RingElem> ret;
  size_t nVars = CoCoA::NumIndets(polyRing);
  for (size_t i = 0; i < nVars; ++i)
  {
    ret.push_back(CoCoA::RingElem(
        ring, solutionStrs.at(ostring(CoCoA::indet(polyRing, i)))));
  }
  return ret;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
