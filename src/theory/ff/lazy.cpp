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
#include "theory/ff/igb.h"
#include "theory/ff/parse.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

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
  std::unordered_set<Node> bits{};
  CocoaEncoder enc(size());
  for (const auto& fact : d_facts)
  {
    enc.addFact(fact);
  }
  enc.endScan();
  for (const auto& fact : d_facts)
  {
    auto bs = parse::bitConstraint(fact);
    if (bs)
    {
      bits.insert(*bs);
    }
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
  // LinearGb lIdeal(" lIdeal", enc.polyRing(), lGens);
  SimpleLinearGb lIdeal(" lIdeal", enc.polyRing(), lGens);
  SparseGb nlIdeal("nlIdeal", enc.polyRing(), nlGens);
  std::vector<IncGb*> ideals{};
  ideals.push_back(&nlIdeal);
  ideals.push_back(&lIdeal);
  nlIdeal.computeBasis();
  lIdeal.computeBasis();
  do
  {
    for (IncGb* ideal : ideals)
    {
      ideal->computeBasis();
      if (ideal->trivial())
      {
        Trace("ffl") << "trivial GB " << ideal->name() << std::endl;
        d_result = Result::UNSAT;
        return;
      }

      for (const auto& p : ideal->basis())
      {
        for (IncGb* i : ideals)
        {
          CoCoA::RingElem reducedP = p;
          {
            CoCoA::RingElem newReducedP = p;

            do
            {
              reducedP = newReducedP;
              for (IncGb* ii : ideals)
              {
                if (ii != i)
                {
                  newReducedP = ii->reduce(newReducedP);
                }
              }
            } while (newReducedP != reducedP);
          }

          if (!CoCoA::IsZero(reducedP) && i->canAdd(reducedP)
              && !i->contains(reducedP))
          {
            Trace("ffl::gb") << i->name() << " += " << reducedP << std::endl;
            i->add(reducedP);
          }
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
            size_t min = std::min(a.getNumChildren(), b.getNumChildren());
            bool allBits = true;
            for (const auto& sum : {a, b})
            {
              for (const auto& c : sum)
              {
                if (!bits.count(c))
                {
                  CoCoA::RingElem p = enc.getTermEncoding(c);
                  CoCoA::RingElem bitConstraint = p * p - p;
                  if (std::any_of(ideals.begin(),
                                  ideals.end(),
                                  [&bitConstraint](const auto& ii) {
                                    return ii->contains(bitConstraint);
                                  }))
                  {
                    Trace("ffl::bitprop")
                        << " bit through GB " << c << std::endl;
                    bits.insert(c);
                  }
                }
                if (!bits.count(c))
                {
                  Trace("ffl::bitprop") << " non-bit " << c << std::endl;
                  allBits = false;
                }
              }
            }

            if (allBits)
            {
              for (size_t k = 0; k < min; ++k)
              {
                CoCoA::RingElem diff =
                    enc.getTermEncoding(a[k]) - enc.getTermEncoding(b[k]);
                for (IncGb* ideal2 : ideals)
                {
                  if (ideal2->canAdd(diff) && !ideal2->contains(diff))
                  {
                    Trace("ffl::bitprop")
                        << ideal2->name() << " += " << diff << std::endl;
                    ideal2->add(diff);
                  }
                }
              }

              if (a.getNumChildren() != min || b.getNumChildren() != min)
              {
                size_t max = a.getNumChildren();
                Node n = a;
                if (b.getNumChildren() > max)
                {
                  max = b.getNumChildren();
                  n = b;
                }
                for (size_t k = min; k < max; ++k)
                {
                  CoCoA::RingElem isZero = enc.getTermEncoding(n[k]);
                  for (IncGb* ideal2 : ideals)
                  {
                    if (ideal2->canAdd(isZero) && !ideal2->contains(isZero))
                    {
                      Trace("ffl::bitprop")
                          << ideal2->name() << " += " << isZero << std::endl;
                      ideal2->add(isZero);
                    }
                  }
                }
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
