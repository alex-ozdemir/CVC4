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
 * Finite fields UNSAT core construction
 */

#include "theory/ff/trace.h"

#include <CoCoA/TmpGPoly.H>

#include <functional>
#include <sstream>

#include "smt/assertions.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

const std::string INPUT = "!!INPUT";

template <typename T>
std::string ostring(const T& t)
{
  std::ostringstream o;
  o << t;
  return o.str();
}

Tracer::Tracer(){};

void Tracer::initFunctionPointers()
{
  Assert(!CoCoA::handlersInited);

  Tracer* t = this;

  CoCoA::handlersInited = true;
  CoCoA::sPolyHandler = std::function(
      [=](const CoCoA::GPoly* p, const CoCoA::GPoly* q, const CoCoA::GPoly* s) {
        t->sPoly(p, q, s);
      });
  CoCoA::reductionStartHandler =
      std::function([=](const CoCoA::GPoly* p) { t->reductionStart(p); });
  CoCoA::reductionStepHandler =
      std::function([=](const CoCoA::GPoly* p) { t->reductionStep(p); });
  CoCoA::reductionEndHandler =
      std::function([=](const CoCoA::GPoly* p) { t->reductionEnd(p); });
}

void Tracer::reset()
{
  Assert(d_reductionSeq.empty());
  d_graph.clear();
  d_inputs.clear();
};

void Tracer::addInput(const CoCoA::RingElem& i)
{
  Assert(d_graph.count(ostring(i)) == 0);
  Trace("ff::trace") << "input: " << i << std::endl;
  size_t s = d_inputs.size();
  d_inputs[ostring(i)] = s;
  d_graph[ostring(i)] = {};
};

std::vector<size_t> Tracer::trace(const CoCoA::RingElem& i) const
{
  std::vector<size_t> bs;
  std::vector<std::string> q{ostring(i)};
  std::unordered_set<std::string> visited{q.back()};
  while (q.size())
  {
    const std::string t = q.back();
    Trace("ff::trace") << "traceback: " << t << std::endl;
    q.pop_back();
    if (d_inputs.count(t))
    {
      Trace("ff::trace") << " blame" << std::endl;
      bs.push_back(d_inputs.at(t));
    }
    else
    {
      AlwaysAssert(d_graph.count(t) > 0);
      const auto& blames = d_graph.at(t);
      AlwaysAssert(blames.size() > 0);
      for (const auto& b : blames)
      {
        if (!visited.count(b))
        {
          visited.insert(b);
          q.push_back(b);
        }
      }
    }
  }
  return bs;
}

void Tracer::sPoly(const CoCoA::GPoly* p,
                   const CoCoA::GPoly* q,
                   const CoCoA::GPoly* s)
{
  std::string ss = ostring(poly(*s));
  Trace("ff::trace") << "s: " << poly(*p) << ", " << poly(*q) << " -> " << poly(*s) << std::endl;
  if (d_graph.count(ss) == 0)
  {
    Trace("ff::trace") << " keep" << std::endl;
    auto& set = d_graph[ss];
    set.insert(ostring(poly(*p)));
    set.insert(ostring(poly(*q)));
  }
  else
  {
    Trace("ff::trace") << " drop" << std::endl;
  }
}

void Tracer::reductionStart(const CoCoA::GPoly* p)
{
  Assert(d_reductionSeq.empty());
  Trace("ff::trace") << "reduction start: " << poly(*p) << std::endl;
  d_reductionSeq.push_back(ostring(poly(*p)));
}

void Tracer::reductionStep(const CoCoA::GPoly* q)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::trace") << "reduction step: " << poly(*q) << std::endl;
  d_reductionSeq.push_back(ostring(poly(*q)));
}

void Tracer::reductionEnd(const CoCoA::GPoly* r)
{
  Assert(!d_reductionSeq.empty());
  Trace("ff::trace") << "reduction end: " << poly(*r) << std::endl;
  std::string rr = ostring(poly(*r));
  if (d_graph.count(rr) == 0 && rr != d_reductionSeq.front())
  {
    Trace("ff::trace") << " keep" << std::endl;
    auto& set = d_graph[rr];
    for (auto& s : d_reductionSeq)
    {
      set.insert(std::move(s));
    }
  }
  else
  {
    Trace("ff::trace") << " drop" << std::endl;
  }
  d_reductionSeq.clear();
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
