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
 * Black box testing of FF gaussian elimination.
 */

#include <set>

#include "base/output.h"
#include "test.h"
#include "theory/ff/gauss.h"
#include "util/finite_field_value.h"
#include "util/integer.h"

namespace cvc5::internal {

using namespace theory::ff;

namespace test {

class TestGauss : public testing::Test
{
};

TEST_F(TestGauss, fuzzSetGet)
{
  srand(0);
  size_t m = 101;

  size_t mats = 100;
  size_t maxRows = 10;
  size_t maxCols = 10;
  size_t updatesPerMat = 100;
  size_t testsPerUpdate = 10;

  for (size_t matIter = 0; matIter < mats; ++matIter)
  {
    size_t rows = rand() % maxRows + 1;
    size_t cols = rand() % maxCols + 1;
    Matrix mat(m, cols, 0, rows);
    Ffv zero{0, m};
    std::vector<std::vector<Ffv>> refMat{rows, {cols, zero}};
    for (size_t updateIter = 0; updateIter < updatesPerMat; ++updateIter)
    {
      // random update
      size_t r = rand() % rows;
      size_t c = rand() % cols;
      Ffv v(rand() % m, m);
      mat.setEntry(r, c, v);
      refMat[r][c] = v;

      // test updated site
      EXPECT_EQ(mat.getEntry(r, c), v);

      // test random entries
      for (size_t testIter = 0; testIter < testsPerUpdate; ++testIter)
      {
        size_t testR = rand() % rows;
        size_t testC = rand() % cols;
        EXPECT_EQ(mat.getEntry(testR, testC), refMat[testR][testC]);
      }
    }

    // test whole matrix
    for (size_t r = 0; r < rows; ++r)
    {
      for (size_t c = 0; c < cols; ++c)
      {
        EXPECT_EQ(mat.getEntry(r, c), refMat[r][c]);
      }
    }
  }
}

TEST_F(TestGauss, fuzzSetRowGet)
{
  srand(0);
  size_t m = 101;

  size_t mats = 100;
  size_t maxRows = 10;
  size_t maxCols = 10;
  size_t updatesPerMat = 10;
  size_t testsPerUpdate = 7;

  for (size_t matIter = 0; matIter < mats; ++matIter)
  {
    size_t rows = rand() % maxRows + 1;
    size_t cols = rand() % maxCols + 1;
    Matrix mat(m, cols, 0, rows);
    Ffv zero{0, m};
    std::vector<std::vector<Ffv>> refMat{rows, {cols, zero}};
    for (size_t updateIter = 0; updateIter < updatesPerMat; ++updateIter)
    {
      // random row update
      size_t elems = rand() % cols;
      std::set<size_t> colsToUpdate{};
      for (size_t elemIter = 0; elemIter < elems; ++elemIter)
      {
        colsToUpdate.insert(rand() % cols);
      }
      std::vector<std::pair<size_t, Ffv>> row{};
      for (const auto c : colsToUpdate)
      {
        row.emplace_back(c, Ffv(rand() % m, m));
      }
      size_t r = rand() % rows;
      for (size_t c = 0; c < cols; ++c)
      {
        refMat[r][c] = Ffv(0, m);
      }
      for (const auto& p : row)
      {
        refMat[r][p.first] = p.second;
      }
      mat.setRow(r, std::move(row));

      // test updated sites
      for (const auto& c : colsToUpdate)
      {
        EXPECT_EQ(mat.getEntry(r, c), refMat[r][c]);
      }

      // test random entries
      for (size_t testIter = 0; testIter < testsPerUpdate; ++testIter)
      {
        size_t testR = rand() % rows;
        size_t testC = rand() % cols;
        EXPECT_EQ(mat.getEntry(testR, testC), refMat[testR][testC]);
      }
    }

    // test whole matrix
    for (size_t r = 0; r < rows; ++r)
    {
      for (size_t c = 0; c < cols; ++c)
      {
        EXPECT_EQ(mat.getEntry(r, c), refMat[r][c]);
      }
    }
  }
}

TEST_F(TestGauss, fuzzRef)
{
  srand(0);
  size_t m = 101;

  size_t mats = 1000;
  size_t maxRows = 10;
  size_t maxCols = 10;
  size_t nzEntriesPerRow = 3;
  // TraceChannel.on("ff::gauss::ref::debug");
  // TraceChannel.on("ff::gauss::form");

  for (size_t matIter = 0; matIter < mats; ++matIter)
  {
    size_t rows = rand() % maxRows + 1;
    size_t cols = rand() % maxCols + 1;
    size_t protCols = rand() % cols;
    Matrix mat(m, cols, protCols, rows);
    Ffv zero{0, m};
    for (size_t r = 0; r < rows; ++r)
    {
      for (size_t i = 0; i < nzEntriesPerRow; ++i)
      {
        size_t c = rand() % cols;
        Ffv v(rand() % m, m);
        mat.setEntry(r, c, v);
      }
    }

    // std::cerr << mat << std::endl;
    mat.ref();
    // std::cerr << mat << std::endl;
    EXPECT_TRUE(mat.inRef());
  }
}

TEST_F(TestGauss, fuzzRref)
{
  srand(0);
  size_t m = 101;

  size_t mats = 1000;
  size_t maxRows = 10;
  size_t maxCols = 10;
  size_t nzEntriesPerRow = 3;
  // TraceChannel.on("ff::gauss::ref::debug");
  // TraceChannel.on("ff::gauss::form");

  for (size_t matIter = 0; matIter < mats; ++matIter)
  {
    size_t rows = rand() % maxRows + 1;
    size_t cols = rand() % maxCols + 1;
    size_t protCols = rand() % cols;
    Matrix mat(m, cols, protCols, rows);
    Ffv zero{0, m};
    for (size_t r = 0; r < rows; ++r)
    {
      for (size_t i = 0; i < nzEntriesPerRow; ++i)
      {
        size_t c = rand() % cols;
        Ffv v(rand() % m, m);
        mat.setEntry(r, c, v);
      }
    }

    // std::cerr << mat << std::endl;
    mat.rref();
    // std::cerr << mat << std::endl;
    EXPECT_TRUE(mat.inRref());
  }
}

TEST_F(TestGauss, fuzzRrefSolver)
{
  srand(0);
  size_t m = 101;
  size_t iters = 100;
  size_t maxVars = 10;
  size_t eqnsPerVar = 2;

  // TraceChannel.on("ff::gauss::ref::debug");
  // TraceChannel.on("ff::gauss::form");

  for (size_t iter = 0; iter < iters; ++iter)
  {
    size_t vars = rand() % maxVars + 1;
    size_t eqns = eqnsPerVar * vars;
    std::vector<Ffv> solution{};
    for (size_t i = 0; i < vars; ++i)
    {
      solution.emplace_back(rand() % m, m);
    }
    Matrix mat(m, vars + 1, 1, eqns);
    Ffv zero{0, m};
    for (size_t r = 0; r < eqns; ++r)
    {
      Ffv const_(0, m);
      for (size_t c = 0; c < vars; ++c)
      {
        Ffv coeff(rand() % m, m);
        mat.setEntry(r, c, coeff);
        const_ += coeff * solution[c];
      }
      mat.setEntry(r, vars, -const_);
    }

    mat.rref();
    for (size_t i = 0; i < vars; ++i)
    {
      EXPECT_EQ(mat.getEntry(i, vars), solution[i]);
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
