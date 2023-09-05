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
 * incremental Groebner bases
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/igb.h"

// external includes
#include <CoCoA/CpuTimeLimit.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-MinPoly.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/ring.H>

// std includes

// internal includes
#include "base/check.h"
#include "base/output.h"
#include "options/ff_options.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

IncGb::IncGb(double gbTimeout,
             const std::string& name,
             const CoCoA::ring& polyRing,
             const std::vector<CoCoA::RingElem>& gens)
    : d_gbTimeout(gbTimeout),
      d_name(name),
      d_polyRing(polyRing),
      d_i(),
      d_newGens(gens),
      d_basis()
{
}

std::unique_ptr<IncGb> IncGb::copy() const
{
  std::unique_ptr<IncGb> self =
      std::make_unique<SparseGb>(d_gbTimeout, d_name, d_polyRing, d_basis);
  self->computeBasis();
  return self;
}

bool IncGb::contains(const CoCoA::RingElem& e) const
{
  if (!d_i) return false;
  Assert(CoCoA::HasGBasis(*d_i));
  return CoCoA::IsElem(e, *d_i);
}

CoCoA::RingElem IncGb::reduce(const CoCoA::RingElem& e) const
{
  if (!d_i) return e;
  Assert(CoCoA::HasGBasis(*d_i));
  return e % *d_i;
}

bool IncGb::canAdd(const CoCoA::RingElem& e) const { return true; }

bool IncGb::trivial() const
{
  if (!d_i) return false;
  Assert(CoCoA::HasGBasis(*d_i));
  return CoCoA::IsOne(*d_i);
}

void IncGb::add(const CoCoA::RingElem& e)
{
  if (d_i) Assert(CoCoA::HasGBasis(*d_i));
  d_newGens.push_back(e);
}

void IncGb::tracePreComputeBasis() const
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
}

bool IncGb::computeBasis()
{
  if (!hasNewGens()) return true;
  tracePreComputeBasis();
  if (d_i)
  {
    *d_i += CoCoA::ideal(d_newGens);
  }
  else
  {
    d_i = {CoCoA::ideal(d_newGens)};
  }
  if (d_gbTimeout == 0)
  {
    d_basis = CoCoA::ReducedGBasis(*d_i);
  }
  else
  {
    try
    {
      d_basis = CoCoA::GBasis(*d_i, CoCoA::CpuTimeLimit(d_gbTimeout / 1000));
    }
    catch (const CoCoA::TimeoutException&)
    {
      return false;
    }
  }
  d_newGens.clear();
  tracePostComputeBasis();
  return true;
}

void IncGb::tracePostComputeBasis() const
{
  Trace("ffl") << d_name << " GB has size " << d_basis.size() << std::endl;
  if (TraceIsOn("ffl::gb"))
  {
    Trace("ffl::gb") << d_name << " GB:" << std::endl;
    for (const auto& p : d_basis)
    {
      Trace("ffl::gb") << " " << p << std::endl;
    }
  }
}

const std::string& IncGb::name() const { return d_name; }
const CoCoA::ring& IncGb::polyRing() const { return d_polyRing; }

bool IncGb::hasNewGens() const { return d_newGens.size(); }

const std::vector<CoCoA::RingElem>& IncGb::basis() const
{
  if (!d_i) return d_basis;
  Assert(d_newGens.empty());
  Assert(CoCoA::HasGBasis(*d_i));
  return d_basis;
}

bool IncGb::zeroDimensional() const
{
  if (!d_i) return CoCoA::NumIndets(d_polyRing) == 0;
  return CoCoA::IsZeroDim(*d_i);
}

CoCoA::RingElem IncGb::minimalPolynomial(size_t indetIdx) const
{
  Assert(d_i);
  Assert(zeroDimensional());
  Assert(static_cast<long>(indetIdx) < CoCoA::NumIndets(d_polyRing));
  CoCoA::RingElem var = CoCoA::indet(d_polyRing, indetIdx);
  CoCoA::RingElem minPoly = CoCoA::MinPolyQuot(var, *d_i, var);
  Assert(CoCoA::UnivariateIndetIndex(minPoly) == static_cast<long>(indetIdx));
  return minPoly;
}

SparseGb::SparseGb(double gbTimeout,
                   const std::string& name,
                   const CoCoA::ring& polyRing,
                   const std::vector<CoCoA::RingElem>& gens)
    : IncGb(gbTimeout, name, polyRing, gens)
{
}
std::unique_ptr<IncGb> SparseGb::copy() const
{
  std::unique_ptr<SparseGb> self =
      std::make_unique<SparseGb>(d_gbTimeout, d_name, d_polyRing, d_basis);
  self->computeBasis();
  return self;
}

bool SparseGb::canAdd(const CoCoA::RingElem& e) const
{
  return (CoCoA::deg(e) <= 1 && CoCoA::NumTerms(e) <= 2);
}

SimpleLinearGb::SimpleLinearGb(double gbTimeout,
                               const std::string& name,
                               const CoCoA::ring& polyRing,
                               const std::vector<CoCoA::RingElem>& gens)
    : IncGb(gbTimeout, name, polyRing, gens)
{
}

std::unique_ptr<IncGb> SimpleLinearGb::copy() const
{
  std::unique_ptr<SimpleLinearGb> self = std::make_unique<SimpleLinearGb>(
      d_gbTimeout, d_name, d_polyRing, d_basis);
  self->computeBasis();
  return self;
}

bool SimpleLinearGb::canAdd(const CoCoA::RingElem& e) const
{
  return CoCoA::deg(e) <= 1;
}

LinearGb::LinearGb(double gbTimeout,
                   const std::string& name,
                   const CoCoA::ring& polyRing,
                   const std::vector<CoCoA::RingElem>& gens)
    : IncGb(gbTimeout, name, polyRing, gens),
      d_mat(CoCoA::BaseRing(polyRing), CoCoA::NumIndets(polyRing) + 1, 1)
{
}

std::unique_ptr<IncGb> LinearGb::copy() const { Unimplemented(); }

bool LinearGb::computeBasis()
{
  if (!hasNewGens()) return true;
  tracePreComputeBasis();
  for (const auto& p : d_newGens)
  {
    addPolyToMatrix(p);
  }
  d_newGens.clear();
  Trace("ffl") << " Gauss start" << std::endl;
  d_mat.rref();
  Trace("ffl") << " Gauss end" << std::endl;
  std::vector<CoCoA::RingElem> gens{};
  for (size_t i = 0; i < d_mat.rows(); ++i)
  {
    gens.push_back(rowAsPoly(i));
  }
  d_i = CoCoA::ideal(gens);
  d_basis = CoCoA::ReducedGBasis(*d_i);
  tracePostComputeBasis();
  return true;
}

CoCoA::RingElem LinearGb::rowAsPoly(size_t r)
{
  CoCoA::RingElem p(d_polyRing, d_mat.getEntry(r, d_mat.cols() - 1));
  for (const auto& [c, v] : d_mat.getRow(r))
  {
    if (c + 1 < d_mat.cols())
    {
      try
      {
        p += CoCoA::indet(d_polyRing, c) * d_mat.getEntry(r, c);
      }
      catch (const CoCoA::ErrorInfo& e)
      {
        std::cerr << e << std::endl;
      }
    }
  }
  return p;
}

void LinearGb::addPolyToMatrix(const CoCoA::RingElem& e)
{
  size_t r = d_mat.rows();
  d_mat.addRow();
  Assert(CoCoA::deg(e) <= 1) << e;
  for (CoCoA::SparsePolyIter it = CoCoA::BeginIter(e), end = CoCoA::EndIter(e);
       it != end;
       ++it)
  {
    long indetIdx = 0;
    if (CoCoA::IsIndet(indetIdx, CoCoA::PP(it)))
    {
      d_mat.setEntry(r, indetIdx, CoCoA::coeff(it));
    }
    else
    {
      d_mat.setEntry(r, d_mat.cols() - 1, CoCoA::coeff(it));
    }
  }
}

bool LinearGb::canAdd(const CoCoA::RingElem& e) const
{
  return CoCoA::deg(e) <= 1;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
