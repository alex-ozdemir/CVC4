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
 * lazy solver
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/lazy.h"

// external includes
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/ideal.H>

// std includes

// internal includes
#include "theory/ff/cocoa.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

class IncGb
{
 public:
  IncGb(const std::string& name, const std::vector<CoCoA::RingElem>& gens);
  virtual ~IncGb(){};
  virtual bool contains(const CoCoA::RingElem& e) const;
  virtual bool canAdd(const CoCoA::RingElem& e) const;
  bool trivial() const;
  void add(const CoCoA::RingElem& e);
  void reduce();
  const std::string& name() const;
  bool hasNewGens() const;
  const std::vector<CoCoA::RingElem>& basis() const;

 protected:
  std::string d_name;
  CoCoA::ideal d_i;
  std::vector<CoCoA::RingElem> d_newGens{};
};

IncGb::IncGb(const std::string& name, const std::vector<CoCoA::RingElem>& gens)
    : d_name(name), d_i(gens[0]), d_newGens(gens)
{
}
bool IncGb::contains(const CoCoA::RingElem& e) const
{
  Assert(CoCoA::HasGBasis(d_i));
  return CoCoA::IsElem(e, d_i);
}
bool IncGb::canAdd(const CoCoA::RingElem& e) const { return true; }
bool IncGb::trivial() const
{
  Assert(CoCoA::HasGBasis(d_i));
  return CoCoA::IsOne(d_i);
}
void IncGb::add(const CoCoA::RingElem& e)
{
  Assert(CoCoA::HasGBasis(d_i));
  d_newGens.push_back(e);
}
void IncGb::reduce()
{
  if (TraceIsOn("ffl::gb"))
  {
    Trace("ffl::gb") << d_name << " new gens:" << std::endl;
    for (const auto& p : d_newGens)
    {
      Trace("ffl::gb") << " " << p << std::endl;
    }
  }
  Trace("ffl") << "reducing " << d_name << " with " << d_newGens.size()
               << " new gens" << std::endl;
  d_i += CoCoA::ideal(d_newGens);
  auto gb = CoCoA::ReducedGBasis(d_i);
  Trace("ffl") << d_name << " GB has size " << gb.size() << std::endl;
  if (TraceIsOn("ffl::gb"))
  {
    Trace("ffl::gb") << d_name << " GB:" << std::endl;
    for (const auto& p : gb)
    {
      Trace("ffl::gb") << " " << p << std::endl;
    }
  }
}
const std::string& IncGb::name() const { return d_name; }
bool IncGb::hasNewGens() const { return d_newGens.size(); }
const std::vector<CoCoA::RingElem>& IncGb::basis() const
{
  Assert(CoCoA::HasGBasis(d_i));
  return CoCoA::ReducedGBasis(d_i);
}

class SparseGb : public IncGb
{
 public:
  SparseGb(const std::string& name, const std::vector<CoCoA::RingElem>& gens)
      : IncGb(name, gens)
  {
  }
  bool canAdd(const CoCoA::RingElem& e) const override
  {
    return (CoCoA::deg(e) <= 1 && CoCoA::NumTerms(e) <= 2);
  }
};

class LinearGb : public IncGb
{
 public:
  LinearGb(const std::string& name, const std::vector<CoCoA::RingElem>& gens)
      : IncGb(name, gens)
  {
  }
  bool canAdd(const CoCoA::RingElem& e) const override
  {
    return CoCoA::deg(e) <= 1;
  }
};

LazySolver::LazySolver(Env& env, const FfSize& size)
    : EnvObj(env), FieldObj(size)
{
}

void LazySolver::assertFact(TNode fact)
{
  Trace("ffl::fact") << "ffl fact " << fact << std::endl;
  d_facts.push_back(fact);
}

void LazySolver::check()
{
  CocoaEncoder enc(size());
  for (const auto& fact : d_facts)
  {
    enc.addFact(fact);
  }
  enc.endScan();
  for (const auto& fact : d_facts)
  {
    enc.addFact(fact);
  }
  if (TraceIsOn("ffl::poly"))
  {
    Trace("ffl::poly") << "ffl polys:" << std::endl;
    for (const auto& p : enc.polys())
    {
      Trace("ffl::poly") << " " << p << std::endl;
    }
    Trace("ffl::poly") << "ffl bitsums:" << std::endl;
    for (const auto& p : enc.bitsumPolys())
    {
      Trace("ffl::poly") << " " << p << std::endl;
    }
  }
  std::vector<CoCoA::RingElem> nlGens = enc.polys();
  std::vector<CoCoA::RingElem> lGens = enc.bitsumPolys();
  std::vector<Node> bitsums = enc.bitsums();
  for (const auto& p : enc.polys())
  {
    if (CoCoA::deg(p) <= 1)
    {
      lGens.push_back(p);
    }
  }
  LinearGb lIdeal(" lIdeal", lGens);
  SparseGb nlIdeal("nlIdeal", nlGens);
  std::vector<IncGb*> ideals{};
  ideals.push_back(&nlIdeal);
  ideals.push_back(&lIdeal);
  nlIdeal.reduce();
  lIdeal.reduce();
  do
  {
    for (IncGb* ideal : ideals)
    {
      ideal->reduce();
      if (ideal->trivial())
      {
        Trace("ffl") << "trivial GB " << ideal->name();
        d_result = Result::UNSAT;
        return;
      }

      for (const auto& p : ideal->basis())
      {
        for (IncGb* i : ideals)
        {
          if (i->canAdd(p))
          {
            Trace("ffl::gb") << i->name() << " += " << p << std::endl;
          }
          i->add(p);
        }
      }

      for (size_t i = 0; i < bitsums.size(); ++i)
      {
        for (size_t j = 0; j < i; ++j)
        {
          Node a = bitsums[i];
          Node b = bitsums[j];
          CoCoA::RingElem bsDiff =
              enc.getTermEncoding(a) - enc.getTermEncoding(b);
          if (ideal->contains(bsDiff))
          {
            Trace("ffl::bitprop")
                << " (= " << a << "\n    " << b << ")" << std::endl;
            AlwaysAssert(a.getNumChildren() == b.getNumChildren())
                << "Unimplemented";
            for (size_t k = 0; k < a.getNumChildren(); ++k)
            {
              CoCoA::RingElem diff =
                  enc.getTermEncoding(a[k]) - enc.getTermEncoding(b[k]);
              for (IncGb* ideal2 : ideals)
              {
                if (ideal2->canAdd(diff))
                {
                  Trace("ffl::bitprop")
                      << ideal2->name() << " += " << diff << std::endl;
                }
                ideal2->add(diff);
              }
            }
          }
        }
      }
    }
  } while (lIdeal.hasNewGens() || nlIdeal.hasNewGens());
}

void LazySolver::clear()
{
  d_facts.clear();
  d_model.clear();
  d_result = Result::UNKNOWN;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
