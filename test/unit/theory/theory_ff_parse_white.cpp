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
 * Black box testing of ff term parsing.
 */

#include <memory>
#include <utility>

#include "test_with_parser.h"
#include "theory/ff/parse.h"

namespace cvc5::internal {

using namespace theory::ff;

namespace test {

class TestFfNodeParser : public TestWithParser
{
};

TEST_F(TestFfNodeParser, square)
{
  {
    doCommand("(define-sort F () (_ FiniteField 7))");
    doCommand("(declare-const x F)");
    Node x = parseNode("(ff.mul x x)");
    EXPECT_TRUE(parse::square(x).has_value());
  }
}

TEST_F(TestFfNodeParser, xMinusOne)
{
  {
    doCommand("(define-sort F () (_ FiniteField 7))");
    doCommand("(declare-const x F)");
    EXPECT_TRUE(
        parse::xMinusOne(parseNode("(ff.add x (as ff-1 F))")).has_value());
    EXPECT_TRUE(
        parse::xMinusOne(parseNode("(ff.add (as ff-1 F) x)")).has_value());
  }
}

TEST_F(TestFfNodeParser, xXMinusOne)
{
  {
    doCommand("(define-sort F () (_ FiniteField 7))");
    doCommand("(declare-const x F)");
    EXPECT_TRUE(
        parse::xXMinusOne(parseNode("(ff.mul x (ff.add (as ff-1 F) x))"))
            .has_value());
    EXPECT_TRUE(
        parse::xXMinusOne(parseNode("(ff.mul (ff.add (as ff-1 F) x) x)"))
            .has_value());
  }
}

TEST_F(TestFfNodeParser, bitConstraint)
{
  {
    doCommand("(define-sort F () (_ FiniteField 7))");
    doCommand("(declare-const x F)");
    EXPECT_TRUE(
        parse::bitConstraint(
            parseNode("(= (ff.mul x (ff.add (as ff-1 F) x)) (as ff0 F))"))
            .has_value());
    EXPECT_TRUE(
        parse::bitConstraint(
            parseNode("(= (as ff0 F) (ff.mul x (ff.add (as ff-1 F) x)))"))
            .has_value());
    EXPECT_TRUE(
        parse::bitConstraint(parseNode("(= x (ff.mul x x))")).has_value());
    EXPECT_FALSE(
        parse::bitConstraint(parseNode("(= x x (ff.mul x x))")).has_value());
  }
}

TEST_F(TestFfNodeParser, varNeValue)
{
  {
    doCommand("(define-sort F () (_ FiniteField 7))");
    doCommand("(declare-const x F)");
    EXPECT_TRUE(
        parse::varNeValue(parseNode("(not (= x (as ff1 F)))")).has_value());
    EXPECT_TRUE(
        parse::varNeValue(parseNode("(not (= (as ff1 F) x))")).has_value());
    EXPECT_FALSE(parse::varNeValue(parseNode("(= x (as ff1 F))")).has_value());
  }
}

TEST_F(TestFfNodeParser, linearMonomial)
{
  {
    doCommand("(define-sort F () (_ FiniteField 7))");
    doCommand("(declare-const x F)");
    doCommand("(declare-const y F)");
    EXPECT_TRUE(
        parse::linearMonomial(parseNode("(ff.mul x (as ff1 F))")).has_value());
    EXPECT_TRUE(
        parse::linearMonomial(parseNode("(ff.mul (as ff1 F) x)")).has_value());
    EXPECT_TRUE(parse::linearMonomial(parseNode("x")).has_value());
    EXPECT_TRUE(parse::linearMonomial(parseNode("(ff.neg x)")).has_value());
    EXPECT_FALSE(parse::linearMonomial(parseNode("(ff.add x y)")).has_value());
  }
}

TEST_F(TestFfNodeParser, sumLinearMonomial)
{
  {
    doCommand("(define-sort F () (_ FiniteField 7))");
    doCommand("(declare-const x F)");
    doCommand("(declare-const y F)");
    EXPECT_TRUE(parse::sumLinearMonomial(parseNode("(as ff0 F)")).has_value());
    EXPECT_TRUE(parse::sumLinearMonomial(parseNode("(ff.mul x (as ff1 F))"))
                    .has_value());
    EXPECT_TRUE(parse::sumLinearMonomial(parseNode("(ff.mul (as ff1 F) x)"))
                    .has_value());
    EXPECT_TRUE(parse::sumLinearMonomial(parseNode("x")).has_value());
    EXPECT_TRUE(parse::sumLinearMonomial(parseNode("(ff.neg x)")).has_value());
    EXPECT_TRUE(
        parse::sumLinearMonomial(parseNode("(ff.add x y)")).has_value());
    EXPECT_TRUE(
        parse::sumLinearMonomial(parseNode("(ff.add (ff.mul x (as ff1 F)) y)"))
            .has_value());
    EXPECT_TRUE(parse::sumLinearMonomial(
                    parseNode("(ff.add (ff.mul x (as ff1 F)) (ff.neg y))"))
                    .has_value());
  }
}

TEST_F(TestFfNodeParser, linearEq)
{
  {
    doCommand("(define-sort F () (_ FiniteField 7))");
    doCommand("(declare-const x F)");
    doCommand("(declare-const y F)");
    EXPECT_TRUE(parse::linearEq(parseNode("(= x (as ff0 F))")).has_value());
    EXPECT_TRUE(parse::linearEq(parseNode("(= x x)")).has_value());
    EXPECT_TRUE(parse::linearEq(parseNode("(= x y)")).has_value());
    EXPECT_TRUE(
        parse::linearEq(parseNode("(= x (ff.mul (as ff2 F) y))")).has_value());
    EXPECT_TRUE(
        parse::linearEq(parseNode("(= y (ff.mul (as ff2 F) y))")).has_value());
    EXPECT_TRUE(
        parse::linearEq(
            parseNode(
                "(= y (ff.add (ff.mul (as ff4 F) x) (ff.mul (as ff2 F) y)))"))
            .has_value());
    EXPECT_TRUE(
        parse::linearEq(
            parseNode(
                "(= (ff.add (ff.mul (as ff4 F) x) (ff.mul (as ff2 F) y)) y)"))
            .has_value());
    EXPECT_TRUE(
        parse::linearEq(
            parseNode(
                "(= (ff.add (ff.mul (as ff4 F) x) (ff.mul (as ff2 F) y)) y)"))
            .has_value());
  }
}

TEST_F(TestFfNodeParser, bitsConstraint)
{
  {
    doCommand("(define-sort F () (_ FiniteField 103))");
    doCommand("(declare-const x F)");
    doCommand("(declare-const y F)");
    doCommand("(declare-const b0 F)");
    doCommand("(declare-const b1 F)");
    doCommand("(declare-const b2 F)");
    EXPECT_TRUE(parse::bitsConstraint(
                    parseNode("(= x (ff.add (ff.mul (as ff1 F) b0) (ff.mul (as "
                              "ff2 F) b1) (ff.mul (as ff4 F) b2)))"))
                    .has_value());
    EXPECT_TRUE(
        parse::bitsConstraint(
            parseNode(
                "(= (ff.neg x) (ff.add (ff.mul (as ff-1 F) b0) (ff.mul (as "
                "ff-2 F) b1) (ff.mul (as ff-4 F) b2)))"))
            .has_value());
    EXPECT_FALSE(
        parse::bitsConstraint(
            parseNode(
                "(= (ff.add x y) (ff.add (ff.mul (as ff-1 F) b0) (ff.mul (as "
                "ff-2 F) b1) (ff.mul (as ff-4 F) b2)))"))
            .has_value());
    EXPECT_TRUE(
        parse::bitsConstraint(
            parseNode(
                "(= (as ff0 F) (ff.add x (ff.mul (as ff-1 F) b0) (ff.mul (as "
                "ff-2 F) b1) (ff.mul (as ff-4 F) b2)))"))
            .has_value());
  }
}

}  // namespace test
}  // namespace cvc5::internal
