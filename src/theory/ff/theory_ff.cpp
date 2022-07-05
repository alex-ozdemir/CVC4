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
 * Finite fields theory
 */

#include "theory/ff/theory_ff.h"

#include <CoCoA/library.H>

#include <cerrno>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <unordered_map>

#include "expr/node_manager_attributes.h"
#include "expr/node_traversal.h"
#include "options/ff_options.h"
#include "theory/ff/toy_gb.h"
#include "theory/ff/toy_gb_blame.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"
#include "util/cocoa_globals.h"
#include "util/utility.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace ff {

TheoryFiniteFields::TheoryFiniteFields(Env& env,
                                       OutputChannel& out,
                                       Valuation valuation)
    : Theory(THEORY_FF, env, out, valuation),
      d_state(env, valuation),
      d_im(env, *this, d_state, getStatsPrefix(THEORY_FF)),
      d_eqNotify(d_im),
      d_ffFacts(context()),
      d_solution(context()),
      d_stats(statisticsRegistry(), "theory::ff::")
{
  d_theoryState = &d_state;
  d_inferManager = &d_im;
  // must be initialized before using CoCoA.
  initCocoaGlobalManager();
}

TheoryFiniteFields::~TheoryFiniteFields() {}

TheoryRewriter* TheoryFiniteFields::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryFiniteFields::getProofChecker() { return nullptr; }

bool TheoryFiniteFields::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_eqNotify;
  esi.d_name = "theory::ff::ee";
  // TODO: not needed, I think
  // esi.d_notifyNewClass = true;
  // esi.d_notifyMerge = true;
  // esi.d_notifyDisequal = true;
  return true;
}

void TheoryFiniteFields::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_MULT);
  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_NEG);
  d_equalityEngine->addFunctionKind(Kind::FINITE_FIELD_ADD);
}

void TheoryFiniteFields::postCheck(Effort level)
{
  Trace("ff::check") << "ff::check : " << level << std::endl;
  // Handle ff facts
  if (!d_ffFacts.empty() && Theory::fullEffort(level))
  {
    std::optional<std::vector<Node>> conflict = isSat();
    if (conflict.has_value())
    {
      d_im.conflict(NodeManager::currentNM()->mkAnd(*conflict),
                    InferenceId::ARITH_FF);
    }
  }
}

void TheoryFiniteFields::notifyFact(TNode atom,
                                    bool polarity,
                                    TNode fact,
                                    bool isInternal)
{
  Trace("ff::check") << "ff::notifyFact : " << atom << " = " << polarity
                     << std::endl;
  if (polarity)
  {
    d_ffFacts.push_back(atom);
  }
  else
  {
    d_ffFacts.push_back(atom.notNode());
  }
}

bool TheoryFiniteFields::collectModelValues(TheoryModel* m,
                                            const std::set<Node>& termSet)
{
  Trace("ff::model") << "Term set: " << termSet << std::endl;
  for (const auto& node : termSet)
  {
    if (d_solution.get().count(node))
    {
      Node value = d_solution.get().at(node);
      Trace("ff::model") << "Model entry: " << node << " -> " << value
                         << std::endl;
      bool okay = m->assertEquality(node, value, true);
      Assert(okay) << "Our model was rejected";
    }
  }
  // TODO
  return true;
}

void TheoryFiniteFields::computeCareGraph()
{
  // TODO
}

TrustNode TheoryFiniteFields::explain(TNode node)
{
  // TODO
  return TrustNode::null();
}

Node TheoryFiniteFields::getModelValue(TNode node)
{
  // TODO
  return Node::null();
}

void TheoryFiniteFields::preRegisterTerm(TNode node)
{
  // TODO
}

TrustNode TheoryFiniteFields::ppRewrite(TNode n, std::vector<SkolemLemma>& lems)
{
  // TODO
  return TrustNode::null();
}

Theory::PPAssertStatus TheoryFiniteFields::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  TNode in = tin.getNode();
  Trace("ff::pp") << "ff::ppAssert : " << in << std::endl;
  Theory::PPAssertStatus status = Theory::PP_ASSERT_STATUS_UNSOLVED;
  return status;
}

void TheoryFiniteFields::presolve()
{
  // TODO
}

bool TheoryFiniteFields::isEntailed(Node n, bool pol)
{
  // TODO
  return false;
}

CoCoA::RingElem bigPower(CoCoA::RingElem b, CoCoA::BigInt e)
{
  CoCoA::RingElem acc = CoCoA::one(CoCoA::owner(b));
  CoCoA::BigInt two = CoCoA::BigInt(2);
  while (!CoCoA::IsZero(e))
  {
    if (CoCoA::IsOdd(e))
    {
      acc *= b;
      e -= 1;
    }
    b *= b;
    CoCoA::divexact(e, e, two);
  }
  return acc;
}

TheoryFiniteFields::Statistics::Statistics(StatisticsRegistry& registry,
                                           const std::string& prefix)
    : d_numReductions(registry.registerInt(prefix + "num_reductions")),
      d_reductionTime(registry.registerTimer(prefix + "reduction_time")),
      d_modelScriptTime(registry.registerTimer(prefix + "model_script_time"))
{
  Trace("ff::stats") << "Registered 3 stats" << std::endl;
}

// CoCoA symbols must start with a letter and contain only letters and
// underscores.
//
// Thus, our encoding is: v_ESCAPED
// where any underscore or invalid character in NAME is replace in ESCAPED with
// an underscore followed by a base-16 encoding of its ASCII code using
// alphabet abcde fghij klmno p, followed by another _.
//
// Sorry. It sucks, but we don't have much to work with here...
std::string varNameToSymName(const std::string& varName)
{
  std::ostringstream o;
  o << "v_";
  for (const auto c : varName)
  {
    if (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z'))
    {
      o << c;
    }
    else
    {
      uint8_t code = c;
      o << "_"
        << "abcdefghijklmnop"[code & 0x0f]
        << "abcdefghijklmnop"[(code >> 4) & 0x0f] << "_";
    }
  }
  return o.str();
}

std::optional<std::vector<Node>> TheoryFiniteFields::isSat()
{
  const std::vector<Node> assertions(d_ffFacts.begin(), d_ffFacts.end());
  bool sat = isSat(assertions, true);
  if (!sat && options().ff.ffTraceToyGb)
  {
    std::vector<Node> core;
    for (const auto i : d_blame)
    {
      core.push_back(assertions[i]);
    }
    if (TraceIsOn("ff::measure::conflict"))
    {
      Trace("ff::measure::conflict") << "conflict [";
      for (const auto& a : core)
      {
        Trace("ff::measure::conflict") << ", " << a;
      }
      Trace("ff::measure::conflict") << "]" << std::endl;
    }
    return core;
  }
  if (!sat && options().ff.ffMeasureConflictQuality)
  {
    size_t smallest = assertions.size();
    std::vector<Node> smallestAssertions = assertions;
    // Each item is a (idx, bitvec) pair, where only indices post idx in bitvec
    // can be zero'd
    std::vector<std::pair<size_t, std::vector<bool>>> stack;
    stack.push_back(std::make_pair(0, std::vector(assertions.size(), true)));
    while (!stack.empty())
    {
      const size_t idx = stack.back().first;
      const std::vector<bool> include = stack.back().second;
      stack.pop_back();
      std::vector<Node> subAs;
      for (size_t i = 0; i < include.size(); ++i)
      {
        if (include[i])
        {
          subAs.push_back(assertions[i]);
        }
      }
      bool res = isSat(subAs, false);
      if (!res)
      {
        if (subAs.size() < smallest)
        {
          if (TraceIsOn("ff::measure::conflict::steps"))
          {
            Trace("ff::measure::conflict::steps") << "[";
            for (const auto& a : subAs)
            {
              Trace("ff::measure::conflict::steps") << ", " << a;
            }
            Trace("ff::measure::conflict::steps") << "]" << std::endl;
          }
          smallest = subAs.size();
          smallestAssertions = std::move(subAs);
        }
        for (size_t i = idx; i < include.size(); ++i)
        {
          if (include[i])
          {
            std::vector<bool> subInclude = include;
            subInclude[i] = false;
            stack.push_back(std::make_pair(i + 1, std::move(subInclude)));
          }
        }
      }
    }
    Trace("ff::measure::conflict")
        << "size " << smallest << " / " << assertions.size() << std::endl;
    if (TraceIsOn("ff::measure::conflict"))
    {
      Trace("ff::measure::conflict") << "conflict [";
      for (const auto& a : smallestAssertions)
      {
        Trace("ff::measure::conflict") << ", " << a;
      }
      Trace("ff::measure::conflict") << "]" << std::endl;
    }
    return smallestAssertions;
  }
  if (sat)
  {
    return {};
  }
  else
  {
    return std::vector(d_ffFacts.begin(), d_ffFacts.end());
  }
}

bool TheoryFiniteFields::isSat(const std::vector<Node>& assertions,
                               bool constructModel)
{
  std::unordered_set<Node> vars = getVars(assertions);
  std::unordered_set<Integer, IntegerHashFunction> sizes =
      getFieldSizes(assertions);
  if (TraceIsOn("ff::check"))
  {
    Trace("ff::check") << "Vars: " << std::endl;
    for (const auto& v : vars)
    {
      Trace("ff::check") << " - " << v << std::endl;
    }
    Trace("ff::check") << "Sizes: " << std::endl;
    for (const auto& v : sizes)
    {
      Trace("ff::check") << " - " << v << std::endl;
    }
  }
  AlwaysAssert(sizes.size() == 1)
      << "Unsupported: multiple field sizes. See ff::check channel.";
  Integer sizeInternal = *sizes.begin();
  CoCoA::BigInt size = CoCoA::BigIntFromString(sizeInternal.toString());
  CoCoA::QuotientRing ringFp = CoCoA::NewZZmod(size);
  std::unordered_map<std::string, Node> symNameNodes;
  std::vector<Node> nodes;
  std::vector<CoCoA::symbol> symbolVec;
  std::vector<CoCoA::symbol> invSyms;

  // Create true variables
  for (const auto& var : vars)
  {
    const std::string varName = var.getAttribute(expr::VarNameAttr());
    const CoCoA::symbol sym(varNameToSymName(varName));
    std::ostringstream fullSymName;
    fullSymName << sym;
    symbolVec.push_back(sym);
    nodes.push_back(var);
    symNameNodes.insert(std::make_pair(fullSymName.str(), var));
  }

  // Create disequality inversion witnesses
  size_t numDisequalities = countDisequalities(assertions);
  for (size_t i = 0; i < numDisequalities; ++i)
  {
    const CoCoA::symbol sym("invwitness", i);
    symbolVec.push_back(sym);
    invSyms.push_back(sym);
  }

  // Create the polynomial ring and find the variable polynomials
  CoCoA::SparsePolyRing ringPoly = CoCoA::NewPolyRing(ringFp, symbolVec);
  std::unordered_map<Node, CoCoA::RingElem> varPolys;
  for (size_t i = 0; i < nodes.size(); ++i)
  {
    CoCoA::RingElem poly = CoCoA::indet(ringPoly, i);
    varPolys.insert(std::make_pair(nodes[i], poly));
  }
  std::unordered_map<Node, CoCoA::RingElem> nodePolys(varPolys);
  std::vector<CoCoA::RingElem> invPolys;
  for (size_t i = 0; i < numDisequalities; ++i)
  {
    invPolys.push_back(CoCoA::indet(ringPoly, nodePolys.size() + i));
  }

  // Build polynomials for terms
  for (const auto& term : assertions)
  {
    for (const auto& node :
         NodeDfsIterable(term, VisitOrder::POSTORDER, [&nodePolys](TNode nn) {
           return nodePolys.count(nn) > 0;
         }))
    {
      if (node.getType().isFiniteField())
      {
        CoCoA::RingElem poly;
        std::vector<CoCoA::RingElem> subPolys;
        std::transform(node.begin(),
                       node.end(),
                       std::back_inserter(subPolys),
                       [&nodePolys](Node n) { return nodePolys[n]; });
        switch (node.getKind())
        {
          case Kind::FINITE_FIELD_ADD:
            poly = std::accumulate(
                subPolys.begin(),
                subPolys.end(),
                CoCoA::RingElem(ringPoly->myZero()),
                [](CoCoA::RingElem a, CoCoA::RingElem b) { return a + b; });
            break;
          case Kind::FINITE_FIELD_NEG: poly = -subPolys[0]; break;
          case Kind::FINITE_FIELD_MULT:
            poly = std::accumulate(
                subPolys.begin(),
                subPolys.end(),
                CoCoA::RingElem(ringPoly->myOne()),
                [](CoCoA::RingElem a, CoCoA::RingElem b) { return a * b; });
            break;
          case Kind::CONST_FINITE_FIELD:
          {
            CoCoA::BigInt constant = CoCoA::BigIntFromString(
                node.getConst<FiniteField>().getValue().toString());
            poly = ringPoly->myOne() * constant;
            break;
          }
          default:
            Unreachable() << "Invalid finite field kind: " << node.getKind();
        }
        Trace("ff::check::trans")
            << "Translated " << node << "\t-> " << poly << std::endl;
        nodePolys.insert(std::make_pair(node, poly));
      }
    }
  }
  std::vector<CoCoA::RingElem> generators;

  // Add one polynomial per assertion
  size_t disequalityIndex = 0;
  for (const auto& assertion : assertions)
  {
    Trace("ff::check::trans") << "Assertion " << assertion << std::endl;

    CoCoA::RingElem p = ringPoly->myZero();
    switch (assertion.getKind())
    {
      case Kind::EQUAL:
      {
        p = nodePolys[assertion[0]] - nodePolys[assertion[1]];
        Trace("ff::check::trans")
            << "Translated " << assertion << "\t-> " << p << std::endl;
        break;
      }
      case Kind::NOT:
      {
        AlwaysAssert(assertion[0].getKind() == Kind::EQUAL);
        Assert(disequalityIndex < numDisequalities);
        CoCoA::RingElem diff =
            nodePolys[assertion[0][0]] - nodePolys[assertion[0][1]];
        p = diff * invPolys[disequalityIndex] - ringPoly->myOne();
        ++disequalityIndex;
        break;
      }
      default:
        Unhandled() << "Kind " << assertion.getKind()
                    << " in finite field sat check";
    }
    Trace("ff::check::trans")
        << "Translated " << assertion << "\t-> " << p << std::endl;
    generators.push_back(p);
  }

  //  Commented out b/c CoCoA can't handle huge exponents
  //
  //  // Size of multiplicative group
  //  CoCoA::BigInt mSize = size - 1;
  //
  //  // Add one polynomial per variable, to bar solutions in the extension
  //  field
  //  // For variable x, x^(order-1) - 1.
  //  for (size_t i = 0; i < symbolVec.size(); ++i)
  //  {
  //    CoCoA::RingElem x = CoCoA::indet(ringPoly, i);
  //    CoCoA::RingElem x_to_q_less_one = bigPower(x, mSize);
  //    generators.push_back(x_to_q_less_one - CoCoA::one(ringPoly));
  //  }

  CoCoA::ideal ideal = CoCoA::ideal(generators);
  std::vector<CoCoA::RingElem> basis;
  {
    CodeTimer reductionTimer(d_stats.d_reductionTime);
    if (options().ff.ffUseToyGb)
    {
      if (options().ff.ffTraceToyGb)
      {
        d_blame.clear();
        auto o = toyGBasisBlame(ideal);
        basis = std::move(o.first);
        d_blame = std::move(o.second);
        if (options().ff.ffCheckTraceToyGb)
        {
          const auto basis2 = toyGBasis(ideal).first;
          if (basis != basis2)
          {
            std::cerr << "First basis: " << basis << std::endl;
            std::cerr << "Real  basis: " << basis2 << std::endl;
            Assert(false);
          }
        }
      }
      else
      {
        auto o = toyGBasis(ideal);
        basis = std::move(o.first);
        d_blame = std::move(o.second);
      }
    }
    else
    {
      basis = CoCoA::GBasis(ideal);
      for (size_t i = 0; i< generators.size(); ++i)
      {
        d_blame.push_back(i);
      }
    }
  }
  ++d_stats.d_numReductions;
  Trace("ff::check") << "Groebner basis " << d_stats.d_numReductions.get()
                     << " " << basis << std::endl;
  for (const auto& basisPoly : basis)
  {
    if (CoCoA::deg(basisPoly) == 0)
    {
      return false;
    }
  }

  if (!constructModel)
  {
    return true;
  }

  Trace("ff::check") << "No 1 in G-Basis, so proceeding to model extraction"
                     << std::endl;
  Trace("ff::check") << "Using script at: " << FF_MODEL_SCRIPT_PATH
                     << std::endl;

  CodeTimer modelScriptTimer(d_stats.d_modelScriptTime);
  // Write the root-finding problem to a temporary file.
  std::string problemPath = "cvc5-ff-problem-XXXXXX";
  std::unique_ptr<std::fstream> problemFile = openTmpFile(&problemPath);
  *problemFile << "size: " << size << std::endl;
  *problemFile << "variables:";
  for (const auto& symbol : symbolVec)
  {
    *problemFile << " " << symbol;
  }
  *problemFile << std::endl;
  // use the g-basis that we already have.
  for (const auto& basisPoly : basis)
  {
    *problemFile << "polynomial: " << basisPoly << std::endl;
  }
  problemFile->flush();

  // create a temporary file for the solution.
  std::string solutionPath = "cvc5-ff-solution-XXXXXX";
  std::unique_ptr<std::fstream> solutionFile = openTmpFile(&solutionPath);

  // run the script
  std::ostringstream cmdBuilder;
  cmdBuilder << FF_MODEL_SCRIPT_PATH << " -i " << problemPath << " -o "
             << solutionPath;
  std::string cmd = cmdBuilder.str();
  int retValue = std::system(cmd.c_str());
  Assert(retValue == 0) << "Non-zero return code from model script";

  // parse the output
  std::unordered_map<std::string, std::string> solutionStrs;
  while (true)
  {
    std::string var;
    std::string val;
    *solutionFile >> var >> val;
    if (solutionFile->eof())
    {
      break;
    }
    Assert(solutionFile->good())
        << "IO error in reading solution file" << std::strerror(errno);
    Trace("ff::check::model") << var << ": " << val << std::endl;
    solutionStrs.emplace(var, val);
  }

  // The output is non-empty if there are non-extension ("real") roots.
  if (!solutionStrs.size())
  {
    return false;
  }

  std::unordered_map<Node, Node> model;
  NodeManager* nm = NodeManager::currentNM();
  for (const auto& line : solutionStrs)
  {
    if (symNameNodes.count(line.first))
    {
      Node var = symNameNodes[line.first];
      Integer integer(line.second, 10);
      FiniteField literal(integer, sizeInternal);
      Node value = nm->mkConst(literal);
      Trace("ff::check::model") << var << ": " << value << std::endl;
      model.emplace(var, value);
    }
  }
  d_solution = model;

  return true;
}

std::unordered_set<Node> getVars(const std::vector<Node>& terms)
{
  std::unordered_set<Node> vars;
  for (const auto& term : terms)
  {
    for (const auto& node : NodeDfsIterable(term))
    {
      if (node.isVar())
      {
        vars.insert(node);
      }
    }
  }
  return vars;
}

std::unordered_set<Integer, IntegerHashFunction> getFieldSizes(
    const std::vector<Node>& terms)
{
  std::unordered_set<Integer, IntegerHashFunction> sizes = {};
  for (const auto& term : terms)
  {
    for (const auto& node : NodeDfsIterable(term))
    {
      TypeNode ty = node.getType();
      if (ty.isFiniteField())
      {
        sizes.insert(ty.getFiniteFieldSize());
      }
    }
  }
  return sizes;
}

size_t countDisequalities(const std::vector<Node>& terms)
{
  size_t ct = 0;
  for (const auto& term : terms)
  {
    if (term.getKind() == Kind::NOT)
    {
      ++ct;
    }
  }
  return ct;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
