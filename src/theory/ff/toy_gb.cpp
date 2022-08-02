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
 * Toy Groebner basis implementation. Included because Buchberger's algorithm
 * is historically important, and it can be informative to run experiments
 * against it.
 *
 * Mostly a copy of the toy Groebner basis implementation[1] that Anna Bigatti
 * wrote for a tutorial on CoCoA(lib) in 2021[2].
 *
 * [1]: https://cocoa.dima.unige.it/cocoa/tutorials/2021-Kassel/ex-MyGBasis.C
 * [2]: https://cocoa.dima.unige.it/cocoa/tutorials/
 */

#include "theory/ff/toy_gb.h"

#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/TmpGPoly.H>
#include <CoCoA/ring.H>
#include <CoCoA/verbose.H>

#include <iostream>
#include <list>

#include "base/check.h"
#include "base/output.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

long FindReducer(CoCoA::ConstRefRingElem f, const std::vector<CoCoA::RingElem>& v)
{
  if (IsZero(f)) return -1;

  for (long j = 0; j < len(v); ++j)  // 0 to len-1
    if (IsDivisible(LPP(f), LPP(v[j]))) return j;
  return -1;
}

CoCoA::RingElem NRLM(CoCoA::ConstRefRingElem f, const std::vector<CoCoA::RingElem>& v)
{
  const CoCoA::SparsePolyRing P = owner(f);
  CoCoA::RingElem m(P);
  CoCoA::RingElem r = f;

  long j = FindReducer(r, v);
  while (j != -1)
  {
    // use CoCoA handlers, so that the toy GB doesn't need its own tracer
    if (CoCoA::handlersEnabled) CoCoA::reductionStepHandler(v[j]);
    //   m = LM(r)/LM(v[i]);
    P->myDivLM(raw(m), raw(r), raw(v[j]));  // no checks
    r -= m * v[j];
    if (IsZero(r)) break;
    j = FindReducer(r, v);
  }
  return r;
}

CoCoA::RingElem NormalRemainder(CoCoA::ConstRefRingElem f, const std::vector<CoCoA::RingElem>& v)
{
  if (IsZero(f)) return f;
  const CoCoA::SparsePolyRing P = owner(f);
  CoCoA::RingElem ansNR(P);
  CoCoA::RingElem tmpNR = f;

  // use CoCoA handlers, so that the toy GB doesn't need its own tracer
  if (CoCoA::handlersEnabled) CoCoA::reductionStartHandler(f);

  tmpNR = NRLM(f, v);
  while (!IsZero(tmpNR))
  {
    P->myMoveLMToBack(raw(ansNR), raw(tmpNR));
    tmpNR = NRLM(tmpNR, v);
  }
  // use CoCoA handlers, so that the toy GB doesn't need its own tracer
  if (CoCoA::handlersEnabled) CoCoA::reductionEndHandler(ansNR);
  return ansNR;
}

CoCoA::RingElem SPoly(CoCoA::ConstRefRingElem g, CoCoA::ConstRefRingElem h)
{
  const CoCoA::ring P = owner(g);
  CoCoA::PPMonoidElem m = lcm(LPP(g), LPP(h));  // monoid: not implemented in CoCoA-5
  CoCoA::RingElem s = monomial(P, 1 / LC(g), m / LPP(g)) * g
         - monomial(P, 1 / LC(h), m / LPP(h)) * h;
  // use CoCoA handlers, so that the toy GB doesn't need its own tracer
  if (CoCoA::handlersEnabled) CoCoA::sPolyHandler(g, h, s);
  return s;
}

class GBPair
{
 public:
  GBPair(long i, long j);  // usual ctor
  ~GBPair(){};

  long myFirstIndex() const { return myFirst; };    // inline
  long mySecondIndex() const { return mySecond; };  // inline

 private:  // class ready for adding other useful information
  long myFirst;
  long mySecond;
};

GBPair::GBPair(long i1, long i2)
{
  if (i1 >= i2)
    CoCoA_THROW_ERROR("i1 >= i2", "GBPair");  // exit from all functions
  myFirst = i1;
  mySecond = i2;
}

std::ostream& operator<<(std::ostream& out, const GBPair& P)
{
  out << "[" << P.myFirstIndex() << ", " << P.mySecondIndex() << "]";
  return out;
}

std::vector<CoCoA::RingElem> toyGBasis(CoCoA::ideal I)
{
  CoCoA::VerboseLog VERBOSE("MyGBasis: ");
  //  -- INITIALIZATION -----------------------------
  std::vector<CoCoA::RingElem> GB;  // empty
  std::list<GBPair> pairs;   // empty
  CoCoA::RingElem g;
  long index_g;
  for (const auto& f : gens(I))  // minor cleaning on gens(I):
  {
    g = NormalRemainder(f, GB);
    if (not(IsZero(g)))
    {
      GB.push_back(g);
      index_g = len(GB) - 1;
      for (long n = 0; n < index_g; ++n) pairs.push_back(GBPair(n, index_g));
    }
  }
  // VERBOSE(8) << "start\n  GB = " << GB << "\n  pairs = " << pairs << std::endl;
  //   -- MAIN LOOP -----------------------------
  GBPair p(123, 1000);  // not used
  while (!pairs.empty())
  {
    p = pairs.front();
    pairs.pop_front();
    VERBOSE(5) << "--" << p << std::endl;
    g = NormalRemainder(SPoly(GB[p.myFirstIndex()], GB[p.mySecondIndex()]), GB);
    if (!IsZero(g))
    {
      GB.push_back(g);
      if (deg(g) == 0) break;
      index_g = len(GB) - 1;
      for (long n = 0; n < index_g; ++n) pairs.push_back(GBPair(n, index_g));
      VERBOSE(5) << "new LPP --> len(pairs) = " << CoCoA::len(pairs) << std::endl;
    }
  }
  // ensure that if the ideal is trivial, we're done.
  for (const auto& b : GB)
  {
    if (CoCoA::deg(b) == 0)
    {
      CoCoA::RingElem constElem = b;
      CoCoA::ring polyRing = CoCoA::owner(constElem);
      GB.clear();
      CoCoA::RingElem one = polyRing->myOne();
      if (CoCoA::handlersEnabled)
      {
        CoCoA::reductionStartHandler(constElem);
        CoCoA::reductionEndHandler(one);
      }
      GB.push_back(one);
      break;
    }
  }
  return GB;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
