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
 * gaussian elimination in FF
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__GAUSS_H
#define CVC5__THEORY__FF__GAUSS_H

// external includes

// std includes
#include <iosfwd>
#include <optional>
#include <vector>

// internal includes
#include "util/finite_field_value.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/** ff value */
using Ffv = FiniteFieldValue;
/** entry in a sparse ff row (column number, value) */
using Entry = std::pair<size_t, Ffv>;
/** a sparse ff row */
using Row = std::vector<Entry>;

class Matrix
{
 public:
  Matrix(const Integer& mod, size_t cols, size_t protCols, size_t rows);
  Matrix(const Matrix&) = delete;
  /** set matrix[r][c] = v */
  void setEntry(size_t r, size_t c, const Ffv& v);
  /** set matrix[r] = row */
  void setRow(size_t r, std::vector<std::pair<size_t, Ffv>>&& row);
  /** get matrix[r][c] */
  const Ffv& getEntry(size_t r, size_t c) const;
  /** get matrix[r] */
  const std::vector<std::pair<size_t, Ffv>>& getRow(size_t r) const;
  /** convert to row echelon form
   *
   * we require the leading coefficients to be -1, which makes the rest of the
   * row to be interpretable as a substitution.
   * */
  void ref();
  /** reduced-row echelon form
   *
   * like ref, but the substitutions do not include eliminated variables.
   *
   * */
  void rref();
  /** in row echelon form? */
  bool inRef() const;
  /** in reduced row echelon form? */
  bool inRref() const;
  /** columns that can be eliminated */
  size_t elimCols() const { return d_cols - d_protCols; }

  // Getters

  /** number of rows */
  size_t rows() const { return d_rows; }
  /** number of columns */
  size_t cols() const { return d_cols; }
  /** number of protected columns */
  size_t protCols() const { return d_protCols; }
  /** modulus */
  const Integer& mod() const { return d_mod; }

 private:
  /** in REF? and what are the pivot columns? */
  bool inRefWithPivots(std::vector<size_t>& pivotCols) const;
  /** swap r0 and r1 */
  void swapRows(size_t r0, size_t r1);
  /** scale r0 by v */
  void scaleRow(size_t r0, const Ffv& v);
  /** rDst += rSrc * srcMultiple */
  void addRowMultiple(size_t rSrc, size_t rDst, const Ffv& srcMultiple);
  /** assert that there are no explicit zeros */
  void assertNoExplicitZeros() const;

  Integer d_mod;
  Ffv d_zero;
  size_t d_cols;
  size_t d_protCols;
  size_t d_rows;
  /** sparse rows */
  std::vector<Row> d_mat;
};

std::ostream& operator<<(std::ostream& o, const Matrix& m);

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__GAUSS_H */
