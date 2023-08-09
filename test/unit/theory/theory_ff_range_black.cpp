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

#include "test.h"
#include "theory/ff/range.h"
#include "util/integer.h"

namespace cvc5::internal {

using namespace theory::ff;

namespace test {

class TestFfRange : public TestInternal
{
};

void testDiv(const Range& rangeIn, const Integer& qIn)
{
  std::cout << "Dividing range " << rangeIn << " / " << qIn << std::endl;
  // check soundness
  Range out = rangeIn.floorDivideQuotient(qIn);
  std::cout << "        result " << out << std::endl;
  for (Integer i = rangeIn.d_lo; i <= rangeIn.d_hi; i += 1)
  {
    Integer qActual = i.floorDivideQuotient(qIn);
    EXPECT_GE(qActual, out.d_lo);
    EXPECT_LE(qActual, out.d_hi);
  }
  // check tightness above
  bool overflow = false;
  for (Integer i = rangeIn.d_hi + 1; i <= rangeIn.d_hi + qIn; i += 1)
  {
    Integer qActual = i.floorDivideQuotient(qIn);
    if (qActual > out.d_hi)
    {
      overflow = true;
      break;
    }
  }
  EXPECT_TRUE(overflow);
  // check tightness below
  bool underflow = false;
  for (Integer i = rangeIn.d_lo - 1; i >= rangeIn.d_lo - qIn; i -= 1)
  {
    Integer qActual = i.floorDivideQuotient(qIn);
    if (qActual < out.d_lo)
    {
      underflow = true;
      break;
    }
  }
  EXPECT_TRUE(underflow);
}

TEST_F(TestFfRange, rangeQuotients)
{
  {
    testDiv({0, 5}, 3);
    testDiv({-5, 5}, 3);
    testDiv({0, 6}, 3);
    testDiv({-3, 6}, 3);
    testDiv({-3, 11}, 3);
  }
}

}  // namespace test
}  // namespace cvc5::internal
