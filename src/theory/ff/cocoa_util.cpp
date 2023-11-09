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
 * CoCoA utilities
 */

#include "theory/ff/cocoa_util.h"

// external includes
#include <CoCoA/BigIntOps.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-RingElem.H>

// std includes

// internal includes

namespace cvc5::internal {
namespace theory {
namespace ff {

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

FiniteFieldValue cocoaFfToFfVal(const CoCoA::RingElem& elem, const FfSize& size)
{
  return {Integer(extractStr(elem), 10), size};
}

CoCoA::BigInt intToCocoa(const Integer& i)
{
  return CoCoA::BigIntFromString(i.toString());
}

}  // namespace theory
}  // namespace ff
}  // namespace cvc5::internal
