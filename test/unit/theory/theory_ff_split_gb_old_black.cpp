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
 * Black box testing of ff multivariate roots.
 */

#ifdef CVC5_USE_COCOA
#include <CoCoA/BigInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/ring.H>
#include <CoCoA/symbol.H>

#include <memory>
#include <utility>

#include "test_smt.h"
#include "theory/ff/multi_roots.h"
#include "theory/ff/split_gb_old.h"
#include "theory/ff/cocoa_util.h"
#include "util/cocoa_globals.h"

namespace cvc5::internal {

using namespace kind;
using namespace context;
using namespace theory;

namespace test {

class TestTheoryFfSplitGbOld : public TestSmt
{
  void SetUp() override
  {
    TestSmt::SetUp();
    initCocoaGlobalManager();
  }
};

CoCoA::RingElem randCoeff(const CoCoA::ring& polyRing)
{
  return CoCoA::zero(CoCoA::CoeffRing(polyRing)) + rand();
}

CoCoA::RingElem randPoly(const CoCoA::ring& polyRing,
                         size_t degree,
                         size_t terms)
{
  CoCoA::RingElem out = CoCoA::zero(polyRing);
  // CoCoA::RingElem out = CoCoA::zero(polyRing) + randCoeff(polyRing);
  for (size_t ti = 0; ti < terms; ++ti)
  {
    CoCoA::RingElem term = CoCoA::zero(polyRing) + randCoeff(polyRing);
    long tDegree = 1 + (rand() % degree);
    for (long i = 0; i < tDegree; ++i)
    {
      long j = rand() % CoCoA::NumIndets(polyRing);
      term *= CoCoA::indet(polyRing, j);
    }
    out += term;
  }
  return out;
}

CoCoA::RingElem randPolyWithRoot(const CoCoA::ring& polyRing,
                                 size_t degree,
                                 size_t terms,
                                 std::vector<CoCoA::RingElem> root)
{
  CoCoA::RingElem p = randPoly(polyRing, degree, terms);
  CoCoA::RingElem val = ff::cocoaEval(p, root);
  return p - val;
}

TEST_F(TestTheoryFfSplitGbOld, NoSplit)
{
  CoCoA::ring ring = CoCoA::NewZZmod(11);
  {
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("a,b,c");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem a = CoCoA::indet(polyRing, 0);
    CoCoA::RingElem b = CoCoA::indet(polyRing, 1);
    CoCoA::RingElem c = CoCoA::indet(polyRing, 2);

    // single basis, SAT
    {
      // TraceChannel.on("ff::split::mc::debug");
      std::vector<CoCoA::RingElem> gens = {a - 0, b - 1, c - 3};
      std::unique_ptr<ff::IncGb> basis =
          std::make_unique<ff::IncGb>(0, "full", polyRing, gens);
      basis->computeBasis();
      std::vector<std::unique_ptr<ff::IncGb>> toadd{};
      toadd.push_back(std::move(basis));
      ff::SplitGb bases(std::move(toadd));
      auto result = ff::splitModelConstruct(bases, true, true);
      ASSERT_TRUE(result.has_value());
      ff::checkModel(bases, *result);
      ASSERT_EQ(result->at(0), 0);
      ASSERT_EQ(result->at(1), 1);
      ASSERT_EQ(result->at(2), 3);
    }

    // single basis, UNSAT
    {
      // TraceChannel.on("ff::split::mc::debug");
      std::vector<CoCoA::RingElem> gens = {a - 0, b - 1, c - 3, c * c - c};
      std::unique_ptr<ff::IncGb> basis =
          std::make_unique<ff::IncGb>(0, "full", polyRing, gens);
      basis->computeBasis();
      std::vector<std::unique_ptr<ff::IncGb>> toadd{};
      toadd.push_back(std::move(basis));
      ff::SplitGb bases(std::move(toadd));
      auto result = ff::splitModelConstruct(bases, true, true);
      ASSERT_FALSE(result.has_value());
    }
  }
}

TEST_F(TestTheoryFfSplitGbOld, TwoSplit)
{
  CoCoA::ring ring = CoCoA::NewZZmod(11);
  {
    std::vector<CoCoA::symbol> syms = CoCoA::symbols("a,b,c");
    CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
    CoCoA::RingElem a = CoCoA::indet(polyRing, 0);
    CoCoA::RingElem b = CoCoA::indet(polyRing, 1);
    CoCoA::RingElem c = CoCoA::indet(polyRing, 2);
    // two bases, SAT
    {
      // TraceChannel.on("ff::split::mc");
      std::vector<CoCoA::RingElem> gens1 = {a - b, b - c + 3};
      std::unique_ptr<ff::IncGb> basis1 =
          std::make_unique<ff::IncGb>(0, "lin", polyRing, gens1);
      basis1->computeBasis();
      std::vector<CoCoA::RingElem> gens2 = {c * (c - 2)};
      std::unique_ptr<ff::IncGb> basis2 =
          std::make_unique<ff::IncGb>(0, "bit", polyRing, gens2);
      basis2->computeBasis();
      std::vector<std::unique_ptr<ff::IncGb>> toadd{};
      toadd.push_back(std::move(basis1));
      toadd.push_back(std::move(basis2));
      ff::SplitGb bases(std::move(toadd));
      auto result = ff::splitModelConstruct(bases, true, true);
      ASSERT_TRUE(result.has_value());
      ff::checkModel(bases, *result);
    }

    // two bases, UNSAT
    {
      // TraceChannel.on("ff::split::mc");
      std::vector<CoCoA::RingElem> gens1 = {a - b, b - c + 3};
      std::unique_ptr<ff::IncGb> basis1 =
          std::make_unique<ff::IncGb>(0, "lin", polyRing, gens1);
      basis1->computeBasis();
      std::vector<CoCoA::RingElem> gens2 = {a * a - a, c * (c - 2)};
      std::unique_ptr<ff::IncGb> basis2 =
          std::make_unique<ff::IncGb>(0, "bit", polyRing, gens2);
      basis2->computeBasis();
      std::vector<std::unique_ptr<ff::IncGb>> toadd{};
      toadd.push_back(std::move(basis1));
      toadd.push_back(std::move(basis2));
      ff::SplitGb bases(std::move(toadd));
      auto result = ff::splitModelConstruct(bases, true, true);
      ASSERT_FALSE(result.has_value());
    }
  }
}

TEST_F(TestTheoryFfSplitGbOld, RandUnsat)
{
  // two bases, random, likely UNSAT
  size_t n_vars = 6;
  size_t degree = 2;
  size_t n_bases = 2;
  size_t n_terms = 1;
  size_t n_eqns = 1.5 * static_cast<double>(n_vars);
  size_t n_iters = 40;
  size_t modulus = 11;
  CoCoA::ring ring = CoCoA::NewZZmod(modulus);
  std::vector<CoCoA::symbol> syms = CoCoA::SymbolRange("x", 0, n_vars - 1);
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
  srand(0);
  for (bool cegar : {false, true})
  {
    for (bool prop : {false, true})
    {
      for (size_t iter_i = 0; iter_i < n_iters; ++iter_i)
      {
        std::vector<std::vector<CoCoA::RingElem>> gens(n_bases);
        std::vector<CoCoA::RingElem> allGens;
        for (size_t i = 0; i < n_eqns; ++i)
        {
          allGens.push_back(randPoly(polyRing, degree, n_terms));
          size_t j = rand() % n_bases;
          gens[j].push_back(allGens.back());
        }
        std::vector<std::unique_ptr<ff::IncGb>> bases;
        for (size_t i = 0; i < n_bases; ++i)
        {
          bases.emplace_back(std::make_unique<ff::IncGb>(
              0, std::string("num") + std::to_string(i), polyRing, gens[i]));
        }
        bool isSat = ff::commonRoot(CoCoA::ideal(allGens)).size();
        // TraceChannel.on("ff::split::mc");
        ff::SplitGb splitBases(std::move(bases));
        splitBases.computeBasis();
        auto result = ff::splitModelConstruct(splitBases, cegar, prop);
        ASSERT_EQ(result.has_value(), isSat);
        if (result.has_value())
        {
          ff::checkModel(splitBases, *result);
        }
      }
    }
  }
}

TEST_F(TestTheoryFfSplitGbOld, RandSat)
{
  // two bases, random, always SAT
  size_t n_vars = 6;
  size_t degree = 2;
  size_t n_bases = 2;
  size_t n_terms = 2;
  size_t n_eqns = 1.5 * static_cast<double>(n_vars);
  size_t n_iters = 50;
  size_t modulus = 11;
  CoCoA::ring ring = CoCoA::NewZZmod(modulus);
  std::vector<CoCoA::symbol> syms = CoCoA::SymbolRange("x", 0, n_vars - 1);
  CoCoA::PolyRing polyRing = CoCoA::NewPolyRing(ring, syms);
  srand(0);
  for (bool cegar : {false, true})
  {
    for (bool prop : {false, true})
    {
      for (size_t iter_i = 0; iter_i < n_iters; ++iter_i)
      {
        std::vector<CoCoA::RingElem> solution{};
        for (size_t i = 0; i < n_vars; ++i)
        {
          solution.push_back(randCoeff(polyRing));
        }
        std::vector<std::vector<CoCoA::RingElem>> gens(n_bases);
        std::vector<CoCoA::RingElem> allGens;
        for (size_t i = 0; i < n_eqns; ++i)
        {
          allGens.push_back(
              randPolyWithRoot(polyRing, degree, n_terms, solution));
          size_t j = rand() % n_bases;
          gens[j].push_back(allGens.back());
        }
        std::vector<std::unique_ptr<ff::IncGb>> bases;
        for (size_t i = 0; i < n_bases; ++i)
        {
          bases.emplace_back(std::make_unique<ff::IncGb>(
              0, std::string("num") + std::to_string(i), polyRing, gens[i]));
        }
        bool isSat = ff::commonRoot(CoCoA::ideal(allGens)).size();
        // TraceChannel.on("ff::split::mc");
        ff::SplitGb splitBases(std::move(bases));
        splitBases.computeBasis();
        auto result = ff::splitModelConstruct(splitBases, cegar, prop);
        ASSERT_EQ(result.has_value(), isSat);
        if (result.has_value())
        {
          ff::checkModel(splitBases, *result);
        }
      }
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
#endif  // CVC5_USE_COCOA

