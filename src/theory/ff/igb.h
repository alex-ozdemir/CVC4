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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__IGB_H
#define CVC5__THEORY__FF__IGB_H

// external includes
#include <CoCoA/ideal.H>
#include <CoCoA/ring.H>

// std includes
#include <optional>
#include <string>

// internal includes
#include "smt/env_obj.h"
#include "theory/ff/cocoa_gauss.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

class IncGb : EnvObj
{
 public:
  IncGb(Env& env,
        const std::string& name,
        const CoCoA::ring& polyRing,
        const std::vector<CoCoA::RingElem>& gens);
  virtual ~IncGb(){};
  virtual bool contains(const CoCoA::RingElem& e) const;
  CoCoA::RingElem reduce(const CoCoA::RingElem& e) const;
  virtual bool canAdd(const CoCoA::RingElem& e) const;
  virtual bool trivial() const;
  void add(const CoCoA::RingElem& e);
  // returns false if timeout
  virtual bool computeBasis();
  const std::string& name() const;
  bool hasNewGens() const;
  const std::vector<CoCoA::RingElem>& basis() const;

 protected:
  void tracePostComputeBasis() const;
  void tracePreComputeBasis() const;

  std::string d_name;
  CoCoA::ring d_polyRing;
  std::optional<CoCoA::ideal> d_i;
  std::vector<CoCoA::RingElem> d_newGens{};
  std::vector<CoCoA::RingElem> d_basis{};
};

class SparseGb : public IncGb
{
 public:
  SparseGb(Env& env,
           const std::string& name,
           const CoCoA::ring& polyRing,
           const std::vector<CoCoA::RingElem>& gens);
  bool canAdd(const CoCoA::RingElem& e) const override;
};

class SimpleLinearGb : public IncGb
{
 public:
  SimpleLinearGb(Env& env,
                 const std::string& name,
                 const CoCoA::ring& polyRing,
                 const std::vector<CoCoA::RingElem>& gens);
  bool canAdd(const CoCoA::RingElem& e) const override;
};

class LinearGb : public IncGb
{
 public:
  LinearGb(Env& env,
           const std::string& name,
           const CoCoA::ring& polyRing,
           const std::vector<CoCoA::RingElem>& gens);
  bool canAdd(const CoCoA::RingElem& e) const override;
  // bool contains(const CoCoA::RingElem& e) const override;
  // bool trivial() const override;
  bool computeBasis() override;

 private:
  CoCoA::RingElem rowAsPoly(size_t r);
  void addPolyToMatrix(const CoCoA::RingElem& e);
  CocoaMatrix d_mat;
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__IGB_H */

#endif /* CVC5_USE_COCOA */
