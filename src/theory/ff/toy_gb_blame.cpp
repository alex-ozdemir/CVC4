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
 * Toy Groebner basis impl with blame-tracking.
 *
 * Based on the toy Groebner basis implementation[1] that Anna Bigatti wrote
 * for a tutorial on CoCoA(lib) in 2021[2].
 *
 * [1]: https://cocoa.dima.unige.it/cocoa/tutorials/2021-Kassel/ex-MyGBasis.C
 * [2]: https://cocoa.dima.unige.it/cocoa/tutorials/
 */

#include "theory/ff/toy_gb_blame.h"

#include <CoCoA/library.H>

#include <iostream>
#include <set>
#include <utility>

#include "base/check.h"
#include "base/output.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

using namespace std;
using namespace CoCoA;

const size_t NO_BLAME = ~((size_t)0);

class Tracer
{
 private:
  vector<RingElem> elems{};
  size_t n_inputs{0};
  bool inputs_done{false};

  vector<pair<size_t, size_t>> blame{};

 public:
  Tracer() {}
  size_t given(const RingElem& e)
  {
    Assert(!inputs_done);
    elems.push_back(e);
    blame.emplace_back(NO_BLAME, NO_BLAME);
    ++n_inputs;
    Trace("ff::toygb::debug") << "blame gb in: " << e << std::endl;
    return elems.size() - 1;
  }
  size_t deduce(const RingElem& e, size_t blame1, size_t blame2)
  {
    inputs_done = true;
    elems.push_back(e);
    blame.emplace_back(blame1, blame2);
    return elems.size() - 1;
  }
  std::vector<size_t> get_blame(size_t elemId)
  {
    Trace("ff::toygb::debug")
        << "blame gb start: " << elems[elemId] << std::endl;
    set<size_t> visited{};
    vector<size_t> q;
    q.push_back(elemId);
    while (!q.empty())
    {
      elemId = q.back();
      Trace("ff::toygb::debug")
          << "blame gb: " << elemId << ": " << elems[elemId] << std::endl;
      q.pop_back();
      if (visited.count(elemId))
      {
        continue;
      }
      visited.insert(elemId);
      if (blame[elemId].first != NO_BLAME)
      {
        q.push_back(blame[elemId].first);
      }
      if (blame[elemId].second != NO_BLAME)
      {
        q.push_back(blame[elemId].second);
      }
    }
    vector<size_t> out;
    for (size_t id : visited)
    {
      if (id < n_inputs)
      {
        Trace("ff::toygb::debug")
            << "blame gb keep: " << id << ": " << elems[id] << std::endl;
        out.push_back(id);
      }
    }
    return out;
  }
};

using RingElemBlame = pair<RingElem, size_t>;
using ConstRefRingElemBlame = pair<ConstRefRingElem, size_t>;

long FindReducerBlame(ConstRefRingElemBlame f, const vector<RingElemBlame>& v)
{
  if (IsZero(f.first)) return -1;

  for (long j = 0; j < len(v); ++j)  // 0 to len-1
    if (IsDivisible(LPP(f.first), LPP(v[j].first))) return j;
  return -1;
}

RingElemBlame NRLMBlame(ConstRefRingElemBlame f,
                        const vector<RingElemBlame>& v,
                        Tracer& tracer)
{
  const SparsePolyRing P = owner(f.first);
  RingElem m(P);
  RingElemBlame r = f;

  long j = FindReducerBlame(r, v);
  while (j != -1)
  {
    //   m = LM(r)/LM(v[i]);
    P->myDivLM(raw(m), raw(r.first), raw(v[j].first));  // no checks
    r.first -= m * v[j].first;
    r.second = tracer.deduce(r.first, r.second, v[j].second);
    if (IsZero(r.first)) return {zero(P), r.second};
    j = FindReducerBlame(r, v);
  }
  return r;
}

RingElemBlame NormalRemainderBlame(ConstRefRingElemBlame f,
                                   const vector<RingElemBlame>& v,
                                   Tracer& tracer)
{
  if (IsZero(f.first)) return f;
  const SparsePolyRing P = owner(f.first);
  RingElem ansNRpoly(P);
  RingElemBlame ansNR = {ansNRpoly,
                         tracer.deduce(ansNRpoly, NO_BLAME, NO_BLAME)};
  RingElemBlame tmpNR = f;

  tmpNR = NRLMBlame(f, v, tracer);
  while (!IsZero(tmpNR.first))
  {
    size_t id0 = ansNR.second;
    size_t id1 = tmpNR.second;
    P->myMoveLMToBack(raw(ansNR.first), raw(tmpNR.first));
    ansNR.second = tracer.deduce(ansNR.first, id0, id1);
    tmpNR.second = tracer.deduce(tmpNR.first, id0, id1);
    tmpNR = NRLMBlame(tmpNR, v, tracer);
  }
  return ansNR;
}

RingElemBlame SPolyBlame(RingElemBlame g, RingElemBlame h, Tracer& tracer)
{
  const ring P = owner(g.first);
  PPMonoidElem m =
      lcm(LPP(g.first), LPP(h.first));  // monoid: not implemented in CoCoA-5
  RingElem s = monomial(P, 1 / LC(g.first), m / LPP(g.first)) * g.first
               - monomial(P, 1 / LC(h.first), m / LPP(h.first)) * h.first;
  return {s, tracer.deduce(s, g.second, h.second)};
}

class GBPairBlame
{
 public:
  GBPairBlame(pair<long, size_t> i, pair<long, size_t> j);  // usual ctor
  ~GBPairBlame(){};

  pair<long, size_t> myFirstIndex() const { return myFirst; };    // inline
  pair<long, size_t> mySecondIndex() const { return mySecond; };  // inline

 private:  // class ready for adding other useful information
  pair<long, size_t> myFirst;
  pair<long, size_t> mySecond;
};

GBPairBlame::GBPairBlame(pair<long, size_t> i1, pair<long, size_t> i2)
{
  if (i1.first >= i2.first)
    CoCoA_THROW_ERROR("i1 >= i2", "GBPair");  // exit from all functions
  myFirst = i1;
  mySecond = i2;
}

ostream& operator<<(ostream& out, const GBPairBlame& P)
{
  out << "[" << P.myFirstIndex().first << ", " << P.mySecondIndex().first
      << "]";
  return out;
}

pair<vector<RingElem>, vector<size_t>> toyGBasisBlame(ideal I)
{
  Trace("ff::toygb") << "toy gb start" << std::endl;
  VerboseLog VERBOSE("MyGBasis: ");
  //  -- INITIALIZATION -----------------------------
  vector<RingElemBlame> inputs;  // empty
  Tracer tracer;
  for (const auto& fPoly : gens(I))
  {
    inputs.emplace_back(fPoly, tracer.given(fPoly));
  }
  vector<RingElemBlame> GB;  // empty
  list<GBPairBlame> pairs;   // empty
  RingElemBlame g;
  long index_g;
  for (const auto& f : inputs)  // minor cleaning on gens(I):
  {
    g = NormalRemainderBlame(f, GB, tracer);
    if (not(IsZero(g.first)))
    {
      GB.push_back(g);
      index_g = len(GB) - 1;
      for (long n = 0; n < index_g; ++n)
        pairs.push_back(
            GBPairBlame({n, GB[n].second}, {index_g, GB[index_g].second}));
    }
  }
  // VERBOSE(8) << "start\n  GB = " << GB << "\n  pairs = " << pairs << endl;
  //   -- MAIN LOOP -----------------------------
  GBPairBlame p({123, 0}, {1000, 0});  // not used
  while (!pairs.empty())
  {
    p = pairs.front();
    pairs.pop_front();
    VERBOSE(5) << "--" << p << endl;
    g = NormalRemainderBlame(
        SPolyBlame(
            GB[p.myFirstIndex().first], GB[p.mySecondIndex().first], tracer),
        GB,
        tracer);
    Trace("ff::toygb::debug") << "toy gb s: " << g.first << std::endl;
    if (!IsZero(g.first))
    {
      GB.push_back(g);
      if (deg(g.first) == 0) break;
      index_g = len(GB) - 1;
      for (long n = 0; n < index_g; ++n)
        pairs.push_back(
            GBPairBlame({n, GB[n].second}, {index_g, GB[index_g].second}));
      VERBOSE(5) << "new LPP --> len(pairs) = " << len(pairs) << endl;
    }
  }
  vector<RingElem> GBout;  // empty
  std::vector<size_t> blame;
  for (const auto& b : GB)
  {
    Trace("ff::toygb::debug") << "toy gb cp: " << b.first << std::endl;
    GBout.push_back(b.first);
    if (deg(b.first) == 0)
    {
      blame = tracer.get_blame(b.second);
    }
  }
  return {GBout, blame};
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
