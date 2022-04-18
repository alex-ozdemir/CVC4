/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A finite-field element, implemented as a wrapper around Integer.
 */

#include "util/finite_field.h"

#include "base/exception.h"

namespace cvc5::internal {

const Integer& FiniteField::getValue() const { return d_value; }

const Integer& FiniteField::getFieldSize() const { return d_modulus; }

Integer FiniteField::toInteger() const { return d_value; }

Integer FiniteField::toSignedInteger() const
{
  Integer half_modulus = d_modulus.divByPow2(1);
  return (d_value < half_modulus) ? d_value : d_value - d_modulus;
}

std::string FiniteField::toString(unsigned int base) const
{
  return toSignedInteger().toString();
}

size_t FiniteField::hash() const { return d_value.hash() + d_modulus.hash(); }

/* -----------------------------------------------------------------------
 * Operators
 * ----------------------------------------------------------------------- */

/* (Dis)Equality --------------------------------------------------------- */

bool FiniteField::operator==(const FiniteField& y) const
{
  if (d_modulus != y.d_modulus) return false;
  return d_value == y.d_value;
}

bool FiniteField::operator!=(const FiniteField& y) const
{
  if (d_modulus != y.d_modulus) return true;
  return d_value != y.d_value;
}

/* Unsigned Inequality --------------------------------------------------- */

bool FiniteField::operator<(const FiniteField& y) const
{
  return d_value < y.d_value;
}

bool FiniteField::operator<=(const FiniteField& y) const
{
  return d_value <= y.d_value;
}

bool FiniteField::operator>(const FiniteField& y) const
{
  return d_value > y.d_value;
}

bool FiniteField::operator>=(const FiniteField& y) const
{
  return d_value >= y.d_value;
}

/* Arithmetic operations ------------------------------------------------- */

FiniteField FiniteField::operator+(const FiniteField& y) const
{
  CheckArgument(d_modulus == y.d_modulus, y);
  Integer sum = d_value.modAdd(y.d_value, d_modulus);
  return FiniteField(d_modulus, sum);
}

FiniteField FiniteField::operator-(const FiniteField& y) const
{
  CheckArgument(d_modulus == y.d_modulus, y);
  return {d_value - y.d_value, d_modulus};
}

FiniteField FiniteField::operator-() const
{
  return {d_modulus - d_value, d_modulus};
}

FiniteField FiniteField::operator*(const FiniteField& y) const
{
  CheckArgument(d_modulus == y.d_modulus, y);
  Integer prod = d_value.modMultiply(y.d_value, d_modulus);
  return FiniteField(d_modulus, prod);
}

FiniteField FiniteField::operator/(const FiniteField& y) const
{
  return *this * y.recip();
}

FiniteField FiniteField::recip() const
{
  CheckArgument(!d_value.isZero(), *this);
  return {d_value.modInverse(d_modulus), d_modulus};
}

/* -----------------------------------------------------------------------
 * Static helpers.
 * ----------------------------------------------------------------------- */

FiniteField FiniteField::mkZero(const Integer& modulus)
{
  return FiniteField(0, modulus);
}

FiniteField FiniteField::mkOne(const Integer& modulus)
{
  return FiniteField(1, modulus);
}

}  // namespace cvc5::internal
