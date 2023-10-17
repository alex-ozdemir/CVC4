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
#include "options/ff_options.h"
#include "theory/ff/cocoa.h"
#include "theory/ff/igb.h"
#include "theory/ff/parse.h"
#include "theory/ff/split_gb.h"

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
  std::vector<std::unique_ptr<IncGb>> ideals{};
  IncGb* nlIdeal;
  IncGb* lIdeal;
  Trace("ffl") << "using gaussian linear ideal: " << std::boolalpha
               << options().ff.fflLinearGauss << std::endl;
  if (options().ff.fflMcLinear)
  {
    if (options().ff.fflLinearGauss)
    {
      ideals.push_back(std::make_unique<LinearGb>(
          options().ff.fflGbTimeout, "lIdeal ", enc.polyRing(), lGens));
    }
    else
    {
      ideals.push_back(std::make_unique<SimpleLinearGb>(
          options().ff.fflGbTimeout, "lIdeal ", enc.polyRing(), lGens));
    }
    ideals.push_back(std::make_unique<SparseGb>(
        options().ff.fflGbTimeout, "nlIdeal", enc.polyRing(), nlGens));
    lIdeal = &*ideals[0];
    nlIdeal = &*ideals[1];
  }
  else
  {
    ideals.push_back(std::make_unique<SparseGb>(
        options().ff.fflGbTimeout, "nlIdeal", enc.polyRing(), nlGens));
    if (options().ff.fflLinearGauss)
    {
      ideals.push_back(std::make_unique<LinearGb>(
          options().ff.fflGbTimeout, "lIdeal ", enc.polyRing(), lGens));
    }
    else
    {
      ideals.push_back(std::make_unique<SimpleLinearGb>(
          options().ff.fflGbTimeout, "lIdeal ", enc.polyRing(), lGens));
    }
    nlIdeal = &*ideals[0];
    lIdeal = &*ideals[1];
  }
  nlIdeal->computeBasis();
  lIdeal->computeBasis();
  do
  {
    for (const auto& ideal : ideals)
    {
      ideal->computeBasis();
      if (ideal->trivial())
      {
        Trace("ffl") << "trivial GB " << ideal->name() << std::endl;
        d_result = Result::UNSAT;
        return;
      }

      if (options().ff.fflShare)
      {
        for (const auto& p : ideal->basis())
        {
          for (const auto& i : ideals)
          {
            CoCoA::RingElem reducedP = p;
            std::vector<std::pair<CoCoA::RingElem, std::string>> steps;
            if (TraceIsOn("ffl::gb"))
            {
              steps.emplace_back(reducedP, ideal->name());
            }
            {
              CoCoA::RingElem newReducedP = p;
              do
              {
                reducedP = newReducedP;
                for (const auto& ii : ideals)
                {
                  if (ii != i)
                  {
                    newReducedP = ii->reduce(newReducedP);
                    if (TraceIsOn("ffl::gb") && newReducedP != reducedP)
                    {
                      steps.emplace_back(newReducedP, ii->name());
                    }
                  }
                }
              } while (newReducedP != reducedP);
            }

            if (!CoCoA::IsZero(reducedP) && i->canAdd(reducedP)
                && !i->contains(reducedP))
            {
              if (TraceIsOn("ffl::gb"))
              {
                Trace("ffl::gb") << i->name() << " += " << reducedP << std::endl
                                 << "  from " << std::endl;
                for (const auto& [pstep, istep] : steps)
                {
                  Trace("ffl::gb")
                      << "    " << pstep << " (" << istep << ")" << std::endl;
                }
              }
              i->add(reducedP);
            }
          }
        }
      }

      if (options().ff.fflBitProp)
      {
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
              size_t max = std::max(a.getNumChildren(), b.getNumChildren());
              if (max > size().d_val.length())
              {
                Trace("ffl::bitprop") << " bitsum overflow" << std::endl;
                continue;
              }
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

              if (!allBits) continue;

              for (size_t k = 0; k < min; ++k)
              {
                CoCoA::RingElem diff =
                    enc.getTermEncoding(a[k]) - enc.getTermEncoding(b[k]);
                for (const auto& ideal2 : ideals)
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
                Node n = b.getNumChildren() > min ? b : a;
                for (size_t k = min; k < max; ++k)
                {
                  CoCoA::RingElem isZero = enc.getTermEncoding(n[k]);
                  for (const auto& ideal2 : ideals)
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
    if (options().ff.fflCompleteShare)
    {
      auto vars = CoCoA::indets(enc.polyRing());
      std::unordered_set<size_t> constantVars{};
      // if a var is constant in lIdeal, prop that and drop the var
      std::remove_if(vars.begin(),
                     vars.end(),
                     [&lIdeal, &nlIdeal](const CoCoA::RingElem& var) {
                       auto normalForm = lIdeal->normalize(var);
                       if (CoCoA::IsConstant(normalForm))
                       {
                         auto assigment = var - normalForm;
                         if (!nlIdeal->contains(assigment))
                         {
                           nlIdeal->add(assigment);
                           // toAdd.push_back(assigment);
                         }
                         return true;
                       }
                       return false;
                     });
      // only the non-constant vars remain
      // try all pairwise equalities
      for (size_t i = 0, end = vars.size(); i < end; ++i)
      {
        for (size_t j = 0; j < i; ++j)
        {
          auto equal = vars[i] - vars[j];
          if (lIdeal->contains(equal) && !nlIdeal->contains(equal))
          {
            nlIdeal->add(equal);
          }
        }
      }
    }
  } while (lIdeal->hasNewGens() || nlIdeal->hasNewGens());
  Trace("ffl") << "start model construction" << std::endl;
  // attempt model construction
  if (d_result == Result::UNKNOWN)
  {
    size_t linearIdx = options().ff.fflMcLinear ? 0 : 1;
    if (options().ff.fflLinearGauss)
    {
      Trace("ffl") << "switching out linear ideal engine "
                   << ideals[linearIdx]->basis().size() << std::endl;
      // can handle non-linear polys which may arise.
      std::unique_ptr<IncGb> simpleLinear =
          std::make_unique<SimpleLinearGb>(options().ff.fflGbTimeout,
                                           "lIdeal ",
                                           enc.polyRing(),
                                           ideals[linearIdx]->basis());
      simpleLinear->computeBasis();
      ideals[linearIdx] = std::move(simpleLinear);
    }

    SplitGb splitGb(std::move(ideals));
    std::optional<std::vector<CoCoA::RingElem>> root = splitModelConstruct(
        splitGb, options().ff.fflMcCegar, options().ff.fflMcProp);
    if (root.has_value())
    {
      d_result = Result::SAT;
      for (const auto& [indetIdx, varNode] : enc.nodeIndets())
      {
        FiniteFieldValue literal = enc.cocoaFfToFfVal(root.value()[indetIdx]);
        Trace("ff::model") << "Model: " << varNode << " = " << literal
                           << std::endl;
        d_model.insert({varNode, literal});
      }
    }
    else
    {
      d_result = Result::UNSAT;
    }
  }
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
