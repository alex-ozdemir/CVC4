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
 * Toy Groebner basis impl.
 */

#include <iostream>
#include <utility>
#include <set>

#include <CoCoA/library.H>

#include "theory/ff/theory_ff.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace ff {

using namespace std;
using namespace CoCoA;

long FindReducer(ConstRefRingElem f, const vector<RingElem>& v)
{
  if (IsZero(f)) return -1;

  for (long j = 0; j < len(v); ++j)  // 0 to len-1
    if (IsDivisible(LPP(f), LPP(v[j]))) return j;
  return -1;
}

RingElem NRLM(ConstRefRingElem f, const vector<RingElem>& v)
{
  const SparsePolyRing P = owner(f);
  RingElem m(P);
  RingElem r = f;

  long j = FindReducer(r, v);
  while (j != -1)
  {
    //   m = LM(r)/LM(v[i]);
    P->myDivLM(raw(m), raw(r), raw(v[j]));  // no checks
    r -= m * v[j];
    if (IsZero(r)) return zero(P);
    j = FindReducer(r, v);
  }
  return r;
}

RingElem NormalRemainder(ConstRefRingElem f, const vector<RingElem>& v)
{
  if (IsZero(f)) return f;
  const SparsePolyRing P = owner(f);
  RingElem ansNR(P);
  RingElem tmpNR = f;

  tmpNR = NRLM(f, v);
  while (!IsZero(tmpNR))
  {
    P->myMoveLMToBack(raw(ansNR), raw(tmpNR));
    tmpNR = NRLM(tmpNR, v);
  }
  return ansNR;
}

RingElem SPoly(ConstRefRingElem g, ConstRefRingElem h)
{
  const ring P = owner(g);
  PPMonoidElem m = lcm(LPP(g), LPP(h));  // monoid: not implemented in CoCoA-5
  return monomial(P, 1 / LC(g), m / LPP(g)) * g
         - monomial(P, 1 / LC(h), m / LPP(h)) * h;
}

const size_t NO_BLAME = ~((size_t) 0);

class Tracer
{
 private:
  vector<RingElem> elems{};
  vector<pair<size_t, size_t>> blame{};
 public:
  Tracer() {}
  size_t given(const RingElem& e)
  {
    elems.push_back(e);
    blame.emplace_back(NO_BLAME, NO_BLAME);
    return elems.size() - 1;
  }
  size_t deduce(const RingElem& e, size_t blame1, size_t blame2)
  {
    Assert(blame1 != NO_BLAME);
    Assert(blame2 != NO_BLAME);
    elems.push_back(e);
    blame.emplace_back(blame1, blame2);
    return elems.size() - 1;
  }
  std::vector<RingElem> get_blame(size_t elemId)
  {
    set<size_t> visited{};
    vector<size_t> q;
    q.push_back(elemId);
    while (!q.empty())
    {
      elemId = q.back();
      q.pop_back();
      if (visited.count(elemId))
      {
        continue;
      }
      visited.insert(elemId);
      if (blame[elemId].first != NO_BLAME)
      {
        q.push_back(blame[elemId].first);
        q.push_back(blame[elemId].second);
      }
    }
    vector<RingElem> out;
    for (size_t id : visited)
    {
      if (blame[id].first == NO_BLAME)
      {
        out.push_back(elems[id]);
      }
    }
    return out;
  }
};

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

ostream& operator<<(ostream& out, const GBPair& P)
{
  out << "[" << P.myFirstIndex() << ", " << P.mySecondIndex() << "]";
  return out;
}

vector<RingElem> toyGBasis(ideal I)
{
  VerboseLog VERBOSE("MyGBasis: ");
  //  -- INITIALIZATION -----------------------------
  vector<RingElem> GB;  // empty
  list<GBPair> pairs;   // empty
  RingElem g;
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
  //VERBOSE(8) << "start\n  GB = " << GB << "\n  pairs = " << pairs << endl;
  //  -- MAIN LOOP -----------------------------
  GBPair p(123, 1000);  // not used
  while (!pairs.empty())
  {
    p = pairs.front();
    pairs.pop_front();
    VERBOSE(5) << "--" << p << endl;
    g = NormalRemainder(SPoly(GB[p.myFirstIndex()], GB[p.mySecondIndex()]), GB);
    if (!IsZero(g))
    {
      GB.push_back(g);
      index_g = len(GB) - 1;
      for (long n = 0; n < index_g; ++n) pairs.push_back(GBPair(n, index_g));
      VERBOSE(5) << "new LPP --> len(pairs) = " << len(pairs) << endl;
    }
  }
  return GB;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
