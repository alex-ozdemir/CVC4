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
 * Gaussian elimination in CoCoA
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/cocoa_gauss.h"

// external includes
#include <CoCoA/BigInt.H>
#include <CoCoA/MachineInt.H>
#include <CoCoA/QuotientRing.H>
#include <CoCoA/ring.H>

// std includes
#include <iomanip>
#include <sstream>

// internal includes
#include "base/check.h"
#include "base/output.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

namespace {

template <typename O>
std::string extractStr(const O& sym)
{
  std::ostringstream o;
  o << sym;
  return o.str();
}

}  // namespace

CocoaMatrix::CocoaMatrix(const CoCoA::ring& field, size_t cols, size_t protCols)
    : d_field(field),
      d_zero(CoCoA::zero(field)),
      d_cols(cols),
      d_protCols(protCols),
      d_rows(0),
      d_mat()
{
  Assert(d_cols >= d_protCols);
}

void CocoaMatrix::addRow()
{
  d_mat.emplace_back();
  ++d_rows;
}

void CocoaMatrix::setEntry(size_t r, size_t c, const Ffv& v)
{
  Assert(r < d_rows);
  Assert(c < d_cols);
  Entry p{c, v};
  // get first x s.t. pred(p, x) is true.
  auto it = std::upper_bound(
      d_mat[r].begin(), d_mat[r].end(), p, [](const auto& x, const auto& y) {
        return x.first <= y.first;
      });
  if (it == d_mat[r].end() || it->first != c)
  {
    if (!CoCoA::IsZero(v))
    {
      d_mat[r].insert(it, std::move(p));
    }
  }
  else
  {
    if (CoCoA::IsZero(v))
    {
      d_mat[r].erase(it);
    }
    else
    {
      it->second = v;
    }
  }
}

void CocoaMatrix::setRow(size_t r, std::vector<std::pair<size_t, Ffv>>&& row)
{
  row.erase(
      std::remove_if(row.begin(),
                     row.end(),
                     [](const auto& p) { return CoCoA::IsZero(p.second); }),
      row.end());
#ifdef CVC5_ASSERTIONS
  for (size_t i = 0; i < row.size(); ++i)
  {
    Assert(row[i].first < d_cols);
    Assert(!CoCoA::IsZero(row[i].second));
    if (i > 0)
    {
      Assert(row[i - 1].first < row[i].first);
    }
  }
#endif  // CVC5_ASSERTIONS
  d_mat[r] = std::move(row);
}

const Ffv& CocoaMatrix::getEntry(size_t r, size_t c) const
{
  Assert(r < d_rows);
  Assert(c < d_cols);
  Entry p{c, d_zero};
  // get first x s.t. pred(p, x) is true.
  auto it = std::upper_bound(
      d_mat[r].begin(), d_mat[r].end(), p, [](const auto& x, const auto& y) {
        return x.first <= y.first;
      });
  if (it == d_mat[r].end() || it->first != c)
  {
    return d_zero;
  }
  return it->second;
}

const std::vector<std::pair<size_t, Ffv>>& CocoaMatrix::getRow(size_t r) const
{
  Assert(r < d_rows);
  return d_mat[r];
}

void CocoaMatrix::ref()
{
  assertNoExplicitZeros();
  size_t pr = 0;  // pivot row
  size_t pc = 0;  // pivot col
  while (pr < d_rows && pc < elimCols())
  {
    Trace("ff::gauss::ref::debug")
        << "pivot start: pr=" << pr << ", pc=" << pc << std::endl;
    Trace("ff::gauss::ref::debug") << *this << std::endl;
    using Key = Ffv;
    const auto mkKey = [](const Ffv& v) {
      return Key(CoCoA::CanonicalRepr(v));
    };
    // (key, row number, value)
    using PivotCandidate = std::tuple<Key, size_t>;
    std::vector<PivotCandidate> prOptions{};
    for (size_t r = pr; r < d_rows; ++r)
    {
      const Ffv& v = getEntry(r, pc);
      if (!CoCoA::IsZero(v))
      {
        prOptions.emplace_back(mkKey(v), r);
      }
    }
    if (!prOptions.empty())
    {
      const auto& [_, pr2] =
          *std::min_element(prOptions.begin(), prOptions.end());
      Trace("ff::gauss::ref::debug") << " chose pr=" << pr2 << std::endl;
      if (pr2 != pr)
      {
        swapRows(pr, pr2);
        Trace("ff::gauss::ref::debug")
            << "swap " << pr << " <-> " << pr2 << ": " << *this << std::endl;
      }
      scaleRow(pr, -CoCoA::power(getEntry(pr, pc), CoCoA::MachineInt(-1)));
      Assert(CoCoA::IsMinusOne(getEntry(pr, pc)));
      for (size_t i = pr + 1; i < d_rows; ++i)
      {
        Trace("ff::gauss::ref::debug") << " updating row r=" << i << std::endl;
        Ffv scalar = getEntry(i, pc);
        if (!CoCoA::IsZero(scalar))
        {
          addRowMultiple(pr, i, scalar);
        }
        Assert(CoCoA::IsZero(getEntry(i, pc)));
      }
      ++pr;
    }
    ++pc;
  }
  assertNoExplicitZeros();
}

void CocoaMatrix::rref()
{
  ref();
  for (size_t r = d_rows - 1; r < d_rows; --r)
  {
    size_t firstNzC = d_mat[r].empty() ? d_cols : d_mat[r][0].first;
    if (firstNzC < elimCols())
    {
      for (size_t rDst = 0; rDst < r; ++rDst)
      {
        const Ffv& v = getEntry(rDst, firstNzC);
        if (!CoCoA::IsZero(v))
        {
          const Ffv vCopy = v;
          addRowMultiple(r, rDst, vCopy);
        }
      }
    }
  }
  assertNoExplicitZeros();
}

bool CocoaMatrix::inRef() const
{
  std::vector<size_t> pivotCols;
  return inRefWithPivots(pivotCols);
}

bool CocoaMatrix::inRref() const
{
  std::vector<size_t> pivotCols;
  return inRefWithPivots(pivotCols);
  for (size_t c : pivotCols)
  {
    bool found = false;
    for (size_t r = 0; r < d_rows; ++r)
    {
      if (!CoCoA::IsZero(getEntry(r, c)))
      {
        if (found)
        {
          Trace("ff::gauss::form") << " not in RREF b/c pivot col " << c
                                   << " has multiple entries" << std::endl;
          return false;
        }
        found = true;
      }
    }
  }
  return true;
}

std::pair<std::vector<std::pair<size_t, std::vector<std::pair<size_t, Ffv>>>>,
          std::vector<std::vector<std::pair<size_t, Ffv>>>>
CocoaMatrix::output() const
{
  std::vector<std::pair<size_t, std::vector<std::pair<size_t, Ffv>>>> substs{};
  std::vector<std::vector<std::pair<size_t, Ffv>>> eqns{};
  for (size_t r = 0; r < d_rows; ++r)
  {
    if (!d_mat[r].empty())
    {
      size_t firstC = d_mat[r][0].first;
      if (firstC < elimCols())
      {
        substs.emplace_back(firstC, d_mat[r]);
        Assert(CoCoA::IsMinusOne(substs.back().second[0].second));
        substs.back().second.erase(substs.back().second.begin());
      }
      else
      {
        eqns.push_back(d_mat[r]);
      }
    }
  }
  return {std::move(substs), std::move(eqns)};
}

std::string CocoaMatrix::toString() const
{
  std::stringstream o{};
  o << *this;
  return o.str();
}

/** r * k */
Row scaleRow(const Row& r, const Ffv& k)
{
  Row out{};
  for (const auto& [c, v] : r)
  {
    out.emplace_back(c, v * k);
  }
  return out;
}

/** r0 + r1 * k */
Row addScaleRows(const Row& r0, const Row& r1, const Ffv& k)
{
  Assert(!CoCoA::IsZero(k));
  Row out{};
  size_t i0 = 0, i1 = 0;
  while (i0 < r0.size() && i1 < r1.size())
  {
    const auto& [c0, v0] = r0[i0];
    const auto& [c1, v1] = r1[i1];
    if (c0 < c1)
    {
      ++i0;
      out.emplace_back(c0, v0);
    }
    else if (c1 < c0)
    {
      ++i1;
      out.emplace_back(c1, v1 * k);
    }
    else
    {
      ++i0;
      ++i1;
      Assert(c0 == c1);
      Ffv v = v0 + v1 * k;
      if (!CoCoA::IsZero(v))
      {
        out.emplace_back(c0, std::move(v));
      }
    }
  }
  if (i0 < r0.size())
  {
    // copy rest of r0
    out.insert(out.end(), std::next(r0.begin(), i0), r0.end());
  }
  else if (i1 < r1.size())
  {
    // copy rest of r1
    for (; i1 < r1.size(); ++i1)
    {
      out.emplace_back(r1[i1].first, r1[i1].second * k);
    }
  }
  return out;
}

bool CocoaMatrix::inRefWithPivots(std::vector<size_t>& pivotCols) const
{
  size_t pc = 0;
  size_t r = 0;
  for (; r < d_rows; ++r)
  {
    if (d_mat[r].empty() || d_mat[r][0].first >= elimCols())
    {
      ++r;
      break;
    }
    size_t firstNzC = d_mat[r][0].first;
    if (firstNzC < pc)
    {
      Trace("ff::gauss::form")
          << " not in REF b/c row " << r << " has first NZ in col " << firstNzC
          << std::endl;
      return false;
    }
    if (!CoCoA::IsMinusOne(getEntry(r, firstNzC)))
    {
      Trace("ff::gauss::form")
          << " not in REF b/c row " << r
          << " has first NZ = " << getEntry(r, firstNzC) << std::endl;
      return false;
    }
    pivotCols.push_back(firstNzC);
    pc = firstNzC + 1;
  }
  for (; r < d_rows; ++r)
  {
    size_t firstNzC = d_mat[r].empty() ? d_cols : d_mat[r][0].first;
    if (firstNzC < elimCols())
    {
      Trace("ff::gauss::form")
          << " not in REF b/c row " << r << " has first NZ in col " << firstNzC
          << std::endl;
      return false;
    }
  }
  return true;
}

void CocoaMatrix::swapRows(size_t r0, size_t r1)
{
  std::swap(d_mat[r0], d_mat[r1]);
}
void CocoaMatrix::scaleRow(size_t r, const Ffv& k)
{
  Assert(!CoCoA::IsZero(k));
  for (auto& [_, v] : d_mat[r])
  {
    v *= k;
  }
}
void CocoaMatrix::addRowMultiple(size_t rSrc,
                                 size_t rDst,
                                 const Ffv& srcMultiple)
{
  Assert(rSrc != rDst);
  Assert(rSrc < d_rows);
  Assert(rDst < d_rows);
  Row newRDst = addScaleRows(d_mat[rDst], d_mat[rSrc], srcMultiple);
  setRow(rDst, std::move(newRDst));
}

void CocoaMatrix::assertNoExplicitZeros() const
{
#ifdef CVC5_ASSERTIONS
  for (size_t r = 0; r < d_rows; ++r)
  {
    for (const auto& [c, v] : d_mat[r])
    {
      Assert(!CoCoA::IsZero(v))
          << "explicit zero at r=" << r << " c=" << c << std::endl;
    }
  }
#endif  // CVC5_ASSERTIONS
}

std::ostream& operator<<(std::ostream& o, const CocoaMatrix& m)
{
  std::vector<std::vector<std::string>> s(
      m.rows(), std::vector<std::string>(m.cols(), std::string()));
  std::vector<size_t> sizes(m.cols(), 0);
  for (size_t r = 0; r < m.rows(); ++r)
  {
    for (size_t c = 0; c < m.cols(); ++c)
    {
      s[r][c] = extractStr(m.getEntry(r, c));
      sizes[c] = std::max(sizes[c], s[r][c].size());
    }
  }
  o << " Matrix " << m.rows() << " x " << m.cols() << ", " << m.protCols()
    << " protected columns, GF(" << m.field() << "), " << std::endl;
  for (size_t r = 0; r < m.rows(); ++r)
  {
    o << '[';
    for (size_t c = 0; c < m.cols(); ++c)
    {
      if (c != 0) o << ' ';
      if (c == m.elimCols())
      {
        o << "| ";
      }
      o << std::setw(sizes[c]) << s[r][c];
    }
    o << ']';
    o << std::endl;
  }
  return o;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
