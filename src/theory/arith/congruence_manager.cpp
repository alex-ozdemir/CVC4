/*********************                                                        */
/*! \file congruence_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Paul Meng, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/congruence_manager.h"

#include "base/output.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/constraint.h"
#include "theory/quantifiers/equality_infer.h"
#include "options/arith_options.h"

namespace CVC4 {
namespace theory {
namespace arith {

ArithCongruenceManager::ArithCongruenceManager(
    context::Context* c,
    context::UserContext* u,
    ConstraintDatabase& cd,
    SetupLiteralCallBack setup,
    const ArithVariables& avars,
    RaiseEqualityEngineConflict raiseConflict,
    ProofNodeManager* pnm)
    : d_inConflict(c),
      d_raiseConflict(raiseConflict),
      d_notify(*this),
      d_keepAlive(c),
      d_propagatations(c),
      d_explanationMap(c),
      d_constraintDatabase(cd),
      d_setupLiteral(setup),
      d_avariables(avars),
      d_ee(d_notify, c, "theory::arith::ArithCongruenceManager", true),
      d_pnm(pnm),
      d_pfGenEe(new EagerProofGenerator(u, pnm)),
      d_pfGenExplain(new EagerProofGenerator(u, pnm)),
      d_pfee(new eq::ProofEqEngine(c, u, d_ee, pnm, options::proofNew()))
{
  d_ee.addFunctionKind(kind::NONLINEAR_MULT);
  d_ee.addFunctionKind(kind::EXPONENTIAL);
  d_ee.addFunctionKind(kind::SINE);
}

ArithCongruenceManager::~ArithCongruenceManager() {}

std::vector<Node> andComponents(TNode an)
{
  auto nm = NodeManager::currentNM();
  if (an == nm->mkConst(true))
  {
    return {};
  }
  else if (an.getKind() != Kind::AND)
  {
    return { an };
  }
  else
  {
    std::vector<Node> a{};
    a.reserve(an.getNumChildren());
    a.insert(a.end(), an.begin(), an.end());
    return a;
  }
}


ArithCongruenceManager::Statistics::Statistics():
  d_watchedVariables("theory::arith::congruence::watchedVariables", 0),
  d_watchedVariableIsZero("theory::arith::congruence::watchedVariableIsZero", 0),
  d_watchedVariableIsNotZero("theory::arith::congruence::watchedVariableIsNotZero", 0),
  d_equalsConstantCalls("theory::arith::congruence::equalsConstantCalls", 0),
  d_propagations("theory::arith::congruence::propagations", 0),
  d_propagateConstraints("theory::arith::congruence::propagateConstraints", 0),
  d_conflicts("theory::arith::congruence::conflicts", 0)
{
  smtStatisticsRegistry()->registerStat(&d_watchedVariables);
  smtStatisticsRegistry()->registerStat(&d_watchedVariableIsZero);
  smtStatisticsRegistry()->registerStat(&d_watchedVariableIsNotZero);
  smtStatisticsRegistry()->registerStat(&d_equalsConstantCalls);
  smtStatisticsRegistry()->registerStat(&d_propagations);
  smtStatisticsRegistry()->registerStat(&d_propagateConstraints);
  smtStatisticsRegistry()->registerStat(&d_conflicts);
}

ArithCongruenceManager::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_watchedVariables);
  smtStatisticsRegistry()->unregisterStat(&d_watchedVariableIsZero);
  smtStatisticsRegistry()->unregisterStat(&d_watchedVariableIsNotZero);
  smtStatisticsRegistry()->unregisterStat(&d_equalsConstantCalls);
  smtStatisticsRegistry()->unregisterStat(&d_propagations);
  smtStatisticsRegistry()->unregisterStat(&d_propagateConstraints);
  smtStatisticsRegistry()->unregisterStat(&d_conflicts);
}

ArithCongruenceManager::ArithCongruenceNotify::ArithCongruenceNotify(ArithCongruenceManager& acm)
  : d_acm(acm)
{}

bool ArithCongruenceManager::ArithCongruenceNotify::eqNotifyTriggerEquality(TNode equality, bool value) {
  Debug("arith::congruences") << "ArithCongruenceNotify::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false") << ")" << std::endl;
  if (value) {
    return d_acm.propagate(equality);
  } else {
    return d_acm.propagate(equality.notNode());
  }
}
bool ArithCongruenceManager::ArithCongruenceNotify::eqNotifyTriggerPredicate(TNode predicate, bool value) {
  Unreachable();
}

bool ArithCongruenceManager::ArithCongruenceNotify::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
  Debug("arith::congruences") << "ArithCongruenceNotify::eqNotifyTriggerTermEquality(" << t1 << ", " << t2 << ", " << (value ? "true" : "false") << ")" << std::endl;
  if (value) {
    return d_acm.propagate(t1.eqNode(t2));
  } else {
    return d_acm.propagate(t1.eqNode(t2).notNode());
  }
}
void ArithCongruenceManager::ArithCongruenceNotify::eqNotifyConstantTermMerge(TNode t1, TNode t2) {
  Debug("arith::congruences") << "ArithCongruenceNotify::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << std::endl;
  d_acm.propagate(t1.eqNode(t2));
}
void ArithCongruenceManager::ArithCongruenceNotify::eqNotifyNewClass(TNode t) {
}
void ArithCongruenceManager::ArithCongruenceNotify::eqNotifyPreMerge(TNode t1, TNode t2) {
}
void ArithCongruenceManager::ArithCongruenceNotify::eqNotifyPostMerge(TNode t1, TNode t2) {
}
void ArithCongruenceManager::ArithCongruenceNotify::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
}

void ArithCongruenceManager::raiseConflict(Node conflict){
  Assert(!inConflict());
  Debug("arith::conflict") << "difference manager conflict   " << conflict << std::endl;
  d_inConflict.raise();
  d_raiseConflict.raiseEEConflict(conflict);
}
bool ArithCongruenceManager::inConflict() const{
  return d_inConflict.isRaised();
}

bool ArithCongruenceManager::hasMorePropagations() const {
  return !d_propagatations.empty();
}
const Node ArithCongruenceManager::getNextPropagation() {
  Assert(hasMorePropagations());
  Node prop = d_propagatations.front();
  d_propagatations.dequeue();
  return prop;
}

bool ArithCongruenceManager::canExplain(TNode n) const {
  return d_explanationMap.find(n) != d_explanationMap.end();
}

void ArithCongruenceManager::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_ee.setMasterEqualityEngine(eq);
}

Node ArithCongruenceManager::externalToInternal(TNode n) const{
  Assert(canExplain(n));
  ExplainMap::const_iterator iter = d_explanationMap.find(n);
  size_t pos = (*iter).second;
  return d_propagatations[pos];
}

void ArithCongruenceManager::pushBack(TNode n){
  d_explanationMap.insert(n, d_propagatations.size());
  d_propagatations.enqueue(n);

  ++(d_statistics.d_propagations);
}
void ArithCongruenceManager::pushBack(TNode n, TNode r){
  d_explanationMap.insert(r, d_propagatations.size());
  d_explanationMap.insert(n, d_propagatations.size());
  d_propagatations.enqueue(n);

  ++(d_statistics.d_propagations);
}
void ArithCongruenceManager::pushBack(TNode n, TNode r, TNode w){
  d_explanationMap.insert(w, d_propagatations.size());
  d_explanationMap.insert(r, d_propagatations.size());
  d_explanationMap.insert(n, d_propagatations.size());
  d_propagatations.enqueue(n);

  ++(d_statistics.d_propagations);
}

void ArithCongruenceManager::watchedVariableIsZero(ConstraintCP lb, ConstraintCP ub){
  Assert(lb->isLowerBound());
  Assert(ub->isUpperBound());
  Assert(lb->getVariable() == ub->getVariable());
  Assert(lb->getValue().sgn() == 0);
  Assert(ub->getValue().sgn() == 0);

  ++(d_statistics.d_watchedVariableIsZero);

  ArithVar s = lb->getVariable();
  TNode eq = d_watchedEqualities[s];
  ConstraintCP eqC = d_constraintDatabase.getConstraint(
      s, ConstraintType::Equality, lb->getValue());
  NodeBuilder<> reasonBuilder(Kind::AND);
  auto pfLb = lb->externalExplainByAssertions(reasonBuilder);
  auto pfUb = ub->externalExplainByAssertions(reasonBuilder);
  Node reason = safeConstructNary(reasonBuilder);
  std::shared_ptr<ProofNode> pf{};
  if (options::proofNew())
  {
    pf = d_pnm->mkNode(
        PfRule::TRICHOTOMY, {pfLb, pfUb}, {eqC->getProofLiteral()});
    pf = d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM, pf, {eq});
  }

  d_keepAlive.push_back(reason);
  Trace("arith-ee") << "Asserting an equality on " << s << ", on trichotomy"
                    << std::endl;
  Trace("arith-ee") << "  based on " << lb << std::endl;
  Trace("arith-ee") << "  based on " << ub << std::endl;
  assertionToEqualityEngine(true, s, reason, pf);
}

void ArithCongruenceManager::watchedVariableIsZero(ConstraintCP eq){
  Debug("arith::cong") << "Cong::watchedVariableIsZero: " << *eq << std::endl;

  Assert(eq->isEquality());
  Assert(eq->getValue().sgn() == 0);

  ++(d_statistics.d_watchedVariableIsZero);

  ArithVar s = eq->getVariable();

  //Explain for conflict is correct as these proofs are generated
  //and stored eagerly
  //These will be safe for propagation later as well
  NodeBuilder<> nb(Kind::AND);
  // An open proof of eq from literals now in reason.
  if (Debug.isOn("arith::cong"))
  {
    eq->printProofTree(Debug("arith::cong"));
  }
  auto pf = eq->externalExplainByAssertions(nb);
  if (options::proofNew())
  {
    pf = d_pnm->mkNode(
        PfRule::MACRO_SR_PRED_TRANSFORM, pf, {d_watchedEqualities[s]});
  }
  Node reason = safeConstructNary(nb);

  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(true, s, reason, pf);
}

void ArithCongruenceManager::watchedVariableCannotBeZero(ConstraintCP c){
  Debug("arith::cong") << "Cong::watchedVariableCannotBeZero " << *c
                       << std::endl;
  ++(d_statistics.d_watchedVariableIsNotZero);

  ArithVar s = c->getVariable();

  //Explain for conflict is correct as these proofs are generated and stored eagerly
  //These will be safe for propagation later as well
  NodeBuilder<> nb(Kind::AND);
  // An open proof of eq from literals now in reason.
  auto pf = c->externalExplainByAssertions(nb);
  if (Debug.isOn("arith::cong::notzero"))
  {
    Debug("arith::cong") << "  original proof ";
    pf->printDebug(Debug("arith::cong"));
    Debug("arith::cong") << std::endl;
  }
  Node reason = safeConstructNary(nb);
  if (options::proofNew())
  {
    if (c->getType() == ConstraintType::Disequality)
    {
      Assert(c->getLiteral() == d_watchedEqualities[s].negate());
      // We have to prove equivalence to the watched disequality.
      pf = d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM,
                         pf,
                         {d_watchedEqualities[s].negate()});
    }
    else
    {
      Debug("arith::cong") << "  proof modification needed" << std::endl;

      // Four cases:
      //   c has form x_i = d, d > 0     => multiply c by -1 in Farkas proof
      //   c has form x_i = d, d > 0     => multiply c by 1 in Farkas proof
      //   c has form x_i <= d, d < 0     => multiply c by 1 in Farkas proof
      //   c has form x_i >= d, d > 0     => multiply c by -1 in Farkas proof
      const bool scaleCNegatively = c->getType() == ConstraintType::LowerBound
                                    || (c->getType() == ConstraintType::Equality
                                        && c->getValue().sgn() > 0);
      const int cSign = scaleCNegatively ? -1 : 1;
      TNode isZero = d_watchedEqualities[s];
      const auto isZeroPf = d_pnm->mkAssume(isZero);
      const auto nm = NodeManager::currentNM();
      const auto sumPf = d_pnm->mkNode(
          PfRule::SCALE_SUM_UPPER_BOUNDS,
          {isZeroPf, pf},
          // Trick for getting correct, opposing signs.
          {nm->mkConst(Rational(-1 * cSign)), nm->mkConst(Rational(cSign))});
      const auto botPf = d_pnm->mkNode(
          PfRule::MACRO_SR_PRED_TRANSFORM, sumPf, {nm->mkConst(false)});
      std::vector<Node> assumption = {isZero};
      pf = d_pnm->mkScope(botPf, assumption, false);
      Debug("arith::cong") << "  new proof ";
      pf->printDebug(Debug("arith::cong"));
      Debug("arith::cong") << std::endl;
    }
  }
  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(false, s, reason, pf);
}


bool ArithCongruenceManager::propagate(TNode x){
  Debug("arith::congruenceManager")<< "ArithCongruenceManager::propagate("<<x<<")"<<std::endl;
  if(inConflict()){
    return true;
  }

  Node rewritten = Rewriter::rewrite(x);

  //Need to still propagate this!
  if(rewritten.getKind() == kind::CONST_BOOLEAN){
    pushBack(x);

    if(rewritten.getConst<bool>()){
      return true;
    }else{
      ++(d_statistics.d_conflicts);
      TrustNode trn = explainInternal(x);
      Node conf = flattenAnd(trn.getNode());
      raiseConflict(conf);
      Debug("arith::congruenceManager") << "rewritten to false "<<x<<" with explanation "<< conf << std::endl;
      return false;
    }
  }

  Assert(rewritten.getKind() != kind::CONST_BOOLEAN);

  ConstraintP c = d_constraintDatabase.lookup(rewritten);
  if(c == NullConstraint){
    //using setup as there may not be a corresponding congruence literal yet
    d_setupLiteral(rewritten);
    c = d_constraintDatabase.lookup(rewritten);
    Assert(c != NullConstraint);
  }

  Debug("arith::congruenceManager")<< "x is "
                                   <<  c->hasProof() << " "
                                   << (x == rewritten) << " "
                                   << c->canBePropagated() << " "
                                   << c->negationHasProof() << std::endl;

  if(c->negationHasProof()){
    TrustNode texpC = explainInternal(x);
    Node expC = texpC.getNode();
    ConstraintCP negC = c->getNegation();
    Node neg = negC->externalExplainByAssertions().getNode();
    Node conf = expC.andNode(neg);
    Node final = flattenAnd(conf);

    ++(d_statistics.d_conflicts);
    raiseConflict(final);
    Debug("arith::congruenceManager") << "congruenceManager found a conflict " << final << std::endl;
    return false;
  }

  // Cases for propagation
  // C : c has a proof
  // S : x == rewritten
  // P : c can be propagated
  //
  // CSP
  // 000 : propagate x, and mark C it as being explained
  // 001 : propagate x, and propagate c after marking it as being explained
  // 01* : propagate x, mark c but do not propagate c
  // 10* : propagate x, do not mark c and do not propagate c
  // 11* : drop the constraint, do not propagate x or c

  if(!c->hasProof() && x != rewritten){
    if(c->assertedToTheTheory()){
      pushBack(x, rewritten, c->getWitness());
    }else{
      pushBack(x, rewritten);
    }

    c->setEqualityEngineProof();
    if(c->canBePropagated() && !c->assertedToTheTheory()){

      ++(d_statistics.d_propagateConstraints);
      c->propagate();
    }
  }else if(!c->hasProof() && x == rewritten){
    if(c->assertedToTheTheory()){
      pushBack(x, c->getWitness());
    }else{
      pushBack(x);
    }
    c->setEqualityEngineProof();
  }else if(c->hasProof() && x != rewritten){
    if(c->assertedToTheTheory()){
      pushBack(x);
    }else{
      pushBack(x);
    }
  }else{
    Assert(c->hasProof() && x == rewritten);
  }
  return true;
}

void ArithCongruenceManager::explain(TNode literal, std::vector<TNode>& assumptions) {
  if (literal.getKind() != kind::NOT) {
    d_ee.explainEquality(literal[0], literal[1], true, assumptions);
  } else {
    d_ee.explainEquality(literal[0][0], literal[0][1], false, assumptions);
  }
}

void ArithCongruenceManager::enqueueIntoNB(const std::set<TNode> s, NodeBuilder<>& nb){
  std::set<TNode>::const_iterator it = s.begin();
  std::set<TNode>::const_iterator it_end = s.end();
  for(; it != it_end; ++it) {
    nb << *it;
  }
}

TrustNode ArithCongruenceManager::explainInternal(TNode internal)
{
  return d_pfee->explain(internal);
}

TrustNode ArithCongruenceManager::explain(TNode external)
{
  Trace("arith-ee") << "Ask for explanation of " << external << std::endl;
  Node internal = externalToInternal(external);
  Trace("arith-ee") << "...internal = " << internal << std::endl;
  TrustNode trn = explainInternal(internal);
  if (options::proofNew() && trn.getProven()[1] != external)
  {
    Assert(trn.getKind() == TrustNodeKind::PROP_EXP);
    Assert(trn.getProven().getKind() == Kind::IMPLIES);
    Assert(trn.getGenerator() != nullptr);
    Trace("arith-ee") << "tweaking proof to prove " << external << " not "
                      << trn.getProven()[1] << std::endl;
    std::vector<std::shared_ptr<ProofNode>> assumptionPfs;
    std::vector<Node> assumptions = andComponents(trn.getNode());
    assumptionPfs.push_back(trn.getGenerator()->getProofFor(trn.getProven()));
    for (const auto& a : assumptions)
    {
      assumptionPfs.push_back(
          d_pnm->mkNode(PfRule::TRUE_INTRO, d_pnm->mkAssume(a), {}));
    }
    auto litPf = d_pnm->mkNode(
        PfRule::MACRO_SR_PRED_TRANSFORM, assumptionPfs, {external});
    auto extPf = d_pnm->mkScope(litPf, assumptions);
    return d_pfGenExplain->mkTrustedPropagation(external, trn.getNode(), extPf);
  }
  else
  {
    return trn;
  }
}

void ArithCongruenceManager::explain(TNode external, NodeBuilder<>& out){
  Node internal = externalToInternal(external);

  std::vector<TNode> assumptions;
  explain(internal, assumptions);
  std::set<TNode> assumptionSet;
  //NodeManager* nm = NodeManager::currentNM();
  assumptionSet.insert(assumptions.begin(), assumptions.end());
  //for (TNode a : assumptions)
  //{
  //  // The equality engine has swapped these out of normal form!
  //  // Reorder them.
  //  if (a.getKind() == Kind::EQUAL && a[0].getKind() == Kind::CONST_RATIONAL)
  //  {
  //    Trace("arith-ee") << "Reordering " << a << std::endl;
  //    assumptionSet.insert(nm->mkNode(Kind::EQUAL, a[0][1], a[0][0]));
  //  }
  //  else
  //  {
  //    Trace("arith-ee") << "Not reordering " << a << std::endl;
  //    assumptionSet.insert(a);
  //  }
  //}

  enqueueIntoNB(assumptionSet, out);
}

void ArithCongruenceManager::addWatchedPair(ArithVar s, TNode x, TNode y){
  Assert(!isWatchedVariable(s));

  Debug("arith::congruenceManager")
    << "addWatchedPair(" << s << ", " << x << ", " << y << ")" << std::endl;


  ++(d_statistics.d_watchedVariables);

  d_watchedVariables.add(s);

  Node eq = x.eqNode(y);
  d_watchedEqualities.set(s, eq);
}

void ArithCongruenceManager::assertLitToEqualityEngine(
    Node lit, TNode reason, std::shared_ptr<ProofNode> pf)
{
  bool isEquality = lit.getKind() != Kind::NOT;
  Node eq = isEquality ? lit : lit[0];
  Assert(eq.getKind() == Kind::EQUAL);

  Trace("arith-ee") << "Assert to Eq " << lit
                    << ", reason " << reason << std::endl;
  if (options::proofNew())
  {
    if (CDProof::isSame(lit, reason))
    {
      Trace("arith-pfee") << "Asserting only, b/c implied by symm" << std::endl;
      d_ee.assertEquality(eq, isEquality, reason);
    }
    else if (hasProofFor(lit))
    {
      Trace("arith-pfee") << "Skipping b/c already done" << std::endl;
    }
    else
    {
      if (pf == nullptr)
      {
        pf = proveWithTrustAssume(lit, reason);
      }
      setProofFor(lit, pf);
      Trace("arith-pfee") << "Actually asserting" << std::endl;
      if (Debug.isOn("arith-pfee")) {
        Trace("arith-pfee") << "Proof: ";
        pf->printDebug(Trace("arith-pfee"));
        Trace("arith-pfee") << std::endl;
      }
      d_pfee->assertFact(lit, reason, d_pfGenEe.get());
    }
  }
  else
  {
    d_ee.assertEquality(eq, isEquality, reason);
  }
}

void ArithCongruenceManager::assertionToEqualityEngine(
    bool isEquality, ArithVar s, TNode reason, std::shared_ptr<ProofNode> pf)
{
  Assert(isWatchedVariable(s));

  TNode eq = d_watchedEqualities[s];
  Assert(eq.getKind() == kind::EQUAL);

  Node lit = isEquality ? Node(eq) : eq.notNode();
  Trace("arith-ee") << "Assert to Eq " << eq << ", pol " << isEquality
                    << ", reason " << reason << std::endl;
  assertLitToEqualityEngine(lit, reason, pf);
}


bool ArithCongruenceManager::hasProofFor(TNode f) const
{
  Assert(options::proofNew());
  if (d_pfGenEe->hasProofFor(f))
  {
    return true;
  }
  Node sym = CDProof::getSymmFact(f);
  Assert(!sym.isNull());
  return d_pfGenEe->hasProofFor(sym);
}

void ArithCongruenceManager::setProofFor(TNode f, std::shared_ptr<ProofNode> pf) const
{
  Assert(!hasProofFor(f));
  d_pfGenEe->mkTrustNode(f, pf);
  Node symF = CDProof::getSymmFact(f);
  auto symPf = d_pnm->mkNode(PfRule::SYMM, pf, {});
  d_pfGenEe->mkTrustNode(symF, symPf);
}

std::shared_ptr<ProofNode> ArithCongruenceManager::proveWithTrustAssume(TNode lit, TNode exp)
{
  std::vector<Node> expVec = andComponents(exp);
  std::vector<std::shared_ptr<ProofNode>> assumps;
  for (const auto& e : expVec)
  {
    assumps.push_back(d_pnm->mkAssume(e));
  }
  return d_pnm->mkNode(PfRule::TRUST, assumps, { lit });
}

void ArithCongruenceManager::equalsConstant(ConstraintCP c){
  Assert(c->isEquality());

  ++(d_statistics.d_equalsConstantCalls);
  Debug("equalsConstant") << "equals constant " << c << std::endl;

  ArithVar x = c->getVariable();
  Node xAsNode = d_avariables.asNode(x);
  Node asRational = mkRationalNode(c->getValue().getNoninfinitesimalPart());


  //No guarentee this is in normal form!
  // Note though, that it happens to be in proof normal form!
  Node eq = xAsNode.eqNode(asRational);
  d_keepAlive.push_back(eq);

  NodeBuilder<> nb(Kind::AND);
  auto pf = c->externalExplainByAssertions(nb);
  Node reason = safeConstructNary(nb);
  d_keepAlive.push_back(reason);

  Trace("arith-ee") << "Assert equalsConstant " << eq << ", reason " << reason << std::endl;
  assertLitToEqualityEngine(eq, reason, pf);
}

void ArithCongruenceManager::equalsConstant(ConstraintCP lb, ConstraintCP ub){
  Assert(lb->isLowerBound());
  Assert(ub->isUpperBound());
  Assert(lb->getVariable() == ub->getVariable());

  ++(d_statistics.d_equalsConstantCalls);
  Debug("equalsConstant") << "equals constant " << lb << std::endl
                          << ub << std::endl;

  ArithVar x = lb->getVariable();
  NodeBuilder<> nb(Kind::AND);
  auto pfLb = lb->externalExplainByAssertions(nb);
  auto pfUb = ub->externalExplainByAssertions(nb);
  Node reason = safeConstructNary(nb);

  Node xAsNode = d_avariables.asNode(x);
  Node asRational = mkRationalNode(lb->getValue().getNoninfinitesimalPart());

  //No guarentee this is in normal form!
  // Note though, that it happens to be in proof normal form!
  Node eq = xAsNode.eqNode(asRational);
  std::shared_ptr<ProofNode> pf;
  if (options::proofNew())
  {
    pf = d_pnm->mkNode(PfRule::TRICHOTOMY, { pfLb, pfUb }, { eq });
  }
  d_keepAlive.push_back(eq);
  d_keepAlive.push_back(reason);

  Trace("arith-ee") << "Assert equalsConstant2 " << eq << ", reason " << reason << std::endl;

  assertLitToEqualityEngine(eq, reason, pf);
}

void ArithCongruenceManager::addSharedTerm(Node x){
  d_ee.addTriggerTerm(x, THEORY_ARITH);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
