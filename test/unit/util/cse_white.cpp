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
 * Black box testing of CSE.
 */

#include <memory>
#include <utility>

#include "test_with_parser.h"
#include "util/cse.h"

namespace cvc5::internal {

using namespace util;

namespace test {

class TestCse : public TestWithParser
{
};

TEST_F(TestCse, noOps)
{
  doCommand("(declare-const x Int)");

  {
    Node x = parseNode("(+ x x)");
    EXPECT_EQ(greedyCse(x, kind::ADD), x);
  }

  {
    Node x = parseNode("(+ x (+ x x) x)");
    EXPECT_EQ(greedyCse(x, kind::ADD), x);
  }

  {
    // + would CSE, but * does not
    Node x = parseNode("(+ x (+ x x x) x x x)");
    EXPECT_EQ(greedyCse(x, kind::MULT), x);
  }
}

TEST_F(TestCse, lcss)
{
  doCommand("(declare-const x Int)");
  doCommand("(declare-const y Int)");

  {
    Node a = parseNode("(+ x x)");
    Node b = parseNode("(+ y y)");
    std::tuple<size_t, size_t, size_t> expected = {0, 0, 0};
    EXPECT_EQ(lcss(a, b), expected);
  }

  {
    Node a = parseNode("(+ x x y)");
    Node b = parseNode("(+ x y y)");
    std::tuple<size_t, size_t, size_t> expected = {2, 1, 0};
    EXPECT_EQ(lcss(a, b), expected);
  }
}

TEST_F(TestCse, simple)
{
  doCommand("(declare-const x Int)");
  doCommand("(declare-const y Int)");
  doCommand("(declare-const z Int)");
  doCommand("(declare-const a Int)");

  {
    Node x = parseNode("(= (+ x x y) (+ y x x))");
    Node y = parseNode("(= (+ (+ x x) y) (+ y (+ x x)))");
    EXPECT_EQ(greedyCse(x, kind::ADD), y);
  }

  {
    Node x = parseNode("(= (+ x x y y y) (+ y y y x x))");
    Node y = parseNode("(= (+ (+ x x) (+ y y y)) (+ (+ y y y) (+ x x)))");
    EXPECT_EQ(greedyCse(x, kind::ADD), y);
  }

  {
    Node x = parseNode("(= (+ x x z) (+ (+ x x y) (+ x x a)))");
    Node y = parseNode("(= (+ (+ x x) z) (+ (+ (+ x x) y) (+ (+ x x) a)))");
    EXPECT_EQ(greedyCse(x, kind::ADD), y);
  }

  {
    Node x = parseNode("(= (+ x x z) (+ (+ x x y y) (+ x x y a)))");
    Node y = parseNode("(= (+ (+ x x) z) (+ (+ (+ (+ x x) y) y) (+ (+ (+ x x) y) a)))");
    EXPECT_EQ(greedyCse(x, kind::ADD), y);
  }
}

}  // namespace test
}  // namespace cvc5::internal
