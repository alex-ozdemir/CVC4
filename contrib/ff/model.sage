#!/usr/bin/env sage
"""
Implementation of model-extraction algorithm from
"Solving Zero-dimensional Algebraic Systems" (Lazard, 1992).

Based on sagemath's toy_variety.

Extended to positive-dimension ideal with some hackery.
"""
import sage.rings.polynomial.toy_buchberger as toy_buchberger
from sage.matrix.constructor import diagonal_matrix
from sage.rings.polynomial.multi_polynomial_ideal import MPolynomialIdeal
from sage.rings.polynomial.ideal import Ideal_1poly_field
from sage.rings.ideal import Ideal_pid
from sage.misc.verbose import set_verbose
from typing import Tuple, List
import itertools
import trace
import unittest
import string
import argparse
import sys

def vars_of_poly_or_const(g):
    if hasattr(g, 'variables'):
        return set(g.variables())
    else:
        return set()

def variables_of(gens):
    """ compute the variables used in gens, from greatest to least """
    G = gens if isinstance(gens, (list, tuple)) else gens.gens()
    return list(reversed(sorted(list(set().union(*[vars_of_poly_or_const(g) for g in G])))))

def restrict_vars(gens):
    """ return a ring restricted to the variables of gens """
    G = gens if isinstance(gens, (list, tuple)) else gens.gens()
    ring = G[0].parent()
    variables = [ring.gen(i) for i in range(ring.ngens())]
    to_remove = set(variables) - set(variables_of(G))
    for v in to_remove:
        ring = ring.remove_var(v)
    return ring

def ideal_dimension(I):
    """ return the dimension of a univariate or multivariate ideal, ignoring missing variables

    returns None if the ideal is empty
    """
    ring = I.ring()
    total_vars = ring.ngens()
    if isinstance(I, MPolynomialIdeal):
        dim = I.dimension()
    elif isinstance(I, Ideal_1poly_field):
        # TODO: trivial ideal?
        dim = total_vars - 1
    elif isinstance(I, Ideal_pid):
        if 1 in I:
            dim = -1
        else:
            dim = total_vars
    else:
        assert False, f"Cannot get the dimension of 'ideal' {I} of type {type(I)}"
    if dim == -1:
        return None
    missing_vars = total_vars - len(variables_of(I.gens()))
    return dim - missing_vars


def is_triangular(gens, xs = None):
    """ check whether the greatest variable in gens[i] is the i'th variable """
    G = gens if isinstance(gens, (list, tuple)) else gens.gens()
    if xs is None: xs = variables_of(G)
    n = len(G)
    for i in range(n):
        if any(x in G[i].variables() for x in xs[:i]):
            return False
    return True

def coeff_matrix(gens):
    """ compute a matrix whose rows are independent if gens are

    each column is a monomial in some gen, each row a polynomial, and each cell a coefficient """
    G = gens if isinstance(gens, (list, tuple)) else gens.gens()
    monomials = list(sorted(set().union(*[g.monomials() for g in G])))
    mon_to_idx = {monomials[i]: i for i in range(len(monomials))}
    M = matrix(G[0].base_ring(), len(G), len(monomials))
    for i in range(len(G)):
        for c, m in zip(G[i].coefficients(), G[i].monomials()):
            M[i, mon_to_idx[m]] += c
    return M

def is_independent(gens):
    """ is this polynomial list indepdent? """
    M = coeff_matrix(gens).echelon_form()
    return not any( M.row(i).is_zero() for i in range(M.nrows()) )

def find_lc_coeffs(p, B):
    """ Compute constant coefficients cs such that
    p = cs[0] * B[0] + ... + cs[n-1] * B[n-1]
    """
    G = B if isinstance(B, (list, tuple)) else B.gens()
    R = p.base_ring()
    M = coeff_matrix(G + [p]).augment(diagonal_matrix(R, [1 for _ in range(len(G) + 1)]))
    M.echelonize()
    j = M.ncols() - 1
    n = M.nrows() - 1
    offset = M.ncols() - M.nrows()
    return [M[n, offset + i] / (-M[n,j]) for i in range(len(G))]

def elim_poly(B, x):
    """ Find the minimal-degree polynomial p in x such
    any vector of variable values X in the variety of G
    has X[x] that is a root of p. """
    G = B if isinstance(B, (list, tuple)) else B.gens()
    reduced_x_powers = []
    reduced_x_pow = (x^0).reduce(G)
    while is_independent(reduced_x_powers + [reduced_x_pow]):
        reduced_x_powers.append(reduced_x_pow)
        reduced_x_pow = (x^len(reduced_x_powers)).reduce(G)
    coeffs = find_lc_coeffs(reduced_x_pow, reduced_x_powers)
    return x^len(coeffs) - sum(coeffs[i] * x^i for i in range(len(coeffs)))

def triangular_factorization(B, n=-1, xs=None):
    G = B if isinstance(B, (list, tuple)) else B.gens()
    if xs is None: xs = variables_of(G)
    if len(G) == 0 or is_triangular(G, xs): return [G]
    p = elim_poly(G, xs[n])
    R = p.parent()
    family = []
    for q, _exp in p.factor():
        ideal_I = R.ideal([p.reduce([q]) for p in G])
        if len(ideal_I.gens()) == 1:
            H = ideal_I.gens()[:1]
        else:
            H = ideal_I.groebner_basis()
        T = triangular_factorization(list(H), n - 1, xs)
        family.extend([t + [q] for t in T])
    return family

def variety_zero_dim(ring, B):
    """ Return common roots, a set of vectors.

    Asserts that the dimension of the variety is zero
    """
    G = B if isinstance(B, (list, tuple)) else B.gens()
    I = ring.ideal(G)
    assert ideal_dimension(I) == 0
    basis = I.groebner_basis()
    R = ring.base_ring()
    T = triangular_factorization(basis)
    xs = variables_of(G)
    v = set()
    for Ti in T:
        for x in itertools.product(*[t.univariate_polynomial().roots(ring=R, multiplicities=False) for t in Ti]):
            v.add(tuple(x))
    return v

def variety_elem(ring, B, mapping = {}):
    """ Return a common root, if one can be found.

    A map from variable names to values.
    Return None if no solution can be found.
    """
    mapping = { k: v for k, v in mapping.items() }
    G = B if isinstance(B, (list, tuple)) else B.gens()
    vs = variables_of(G)
    for k in mapping:
        assert k not in vs
    I = ring.ideal(G)
    dim = ideal_dimension(I)
    if dim == 0:
        variety = variety_zero_dim(ring, G)
        if len(variety) == 0:
            return None
        else:
            return dict(list(mapping.items()) + list(zip(map(str, vs), variety.pop())))
    elif dim is None:
        return None
    else:
        b = I.groebner_basis()
        R = I.ring().base_ring()
        for p in b:
            if len(p.variables()) == 1:
                var = str(p.variables()[0])
                for root in p.univariate_polynomial().roots(ring=R, multiplicities=False):
                    m = mapping.copy()
                    m[var] = root
                    GG = [g(**{var: root}) for g in G]
                    common_root = variety_elem(ring, GG, m)
                    if common_root is not None:
                        return common_root
                return None
        var = str(p.variables()[0])
        # better iter order?
        for value in R:
            m = mapping.copy()
            m[var] = value
            GG = [g(**{var: value}) for g in G]
            common_root = variety_elem(ring, GG, m)
            if common_root is not None:
                return common_root
        return None


class MyUnitTests(unittest.TestCase):

    def setUp(self):
        self.order = 17
        self.order = 53
        self.order = 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787 # bls scalar field
        P.<a,b,c,d,e,f,g,h,i,j,k> = PolynomialRing(GF(self.order))
        self.P = P
        self.a = a
        self.b = b
        self.c = c
        self.d = d
        self.e = e
        self.f = f
        self.g = g
        self.h = h
        self.i = i
        self.j = j
        self.k = k
        set_verbose(-1)

    def test_variables_of(self):
        self.assertEqual(variables_of([self.b,self.d]), [self.b, self.d])

    def test_ideal_dimension(self):
        self.assertEqual(ideal_dimension(self.P.ideal([self.a])), 0)
        self.assertEqual(ideal_dimension(self.P.ideal([self.a*self.a])), 0)
        self.assertEqual(ideal_dimension(self.P.ideal([self.a*self.b])), 1)
        self.assertEqual(ideal_dimension(self.P.ideal([self.a*self.b+1, self.a])), None)

    def test_restrict_vars(self):
        ring = restrict_vars([self.a, self.b])
        self.assertEqual(ring.ngens(), 2)

    def test_is_triangular(self):
        self.assertTrue(is_triangular([self.b,self.d]))
        self.assertTrue(not is_triangular([self.d,self.b]))
        self.assertTrue(is_triangular([self.b+self.d^4,self.d]))

    def test_is_triangular(self):
        self.assertEqual(coeff_matrix([self.a,self.b]), matrix([[0,1],[1,0]]))
        self.assertEqual(coeff_matrix([self.a,self.b+self.a]), matrix([[0,1],[1,1]]))
        self.assertEqual(coeff_matrix([self.a,self.b+2*self.a]), matrix([[0,1],[1,2]]))
        self.assertEqual(coeff_matrix([self.a,self.a]), matrix([[1],[1]]))

    def test_is_indepedent(self):
        self.assertTrue(is_independent([self.a, self.b]))
        self.assertTrue(not is_independent([self.a, 2 * self.a]))
        self.assertTrue(is_independent([self.a, 2 * self.a + self.a^2]))
        self.assertTrue(is_independent([self.a, 2 * self.a + self.b]))
        self.assertTrue(not is_independent([self.a, self.a]))
        self.assertTrue(not is_independent([self.c^0, self.c, self.c]))

    def test_lc_coeffs(self):
        self.assertEqual(find_lc_coeffs(self.a, [self.a, self.b, self.c]), [1, 0, 0])
        self.assertEqual(find_lc_coeffs(2*self.a+self.a^2, [self.a, self.b, self.c, self.a+self.a^2]), [1, 0, 0, 1])

    def test_elim_poly(self):
        self.assertEqual(elim_poly(self.P.ideal([self.a^2*(self.a-1)^3*self.b^2*(self.c-3)^3,self.c^2-self.c, (self.a-2)^2*(self.b-1)^3]).groebner_basis(), self.c), self.c^2 - self.c)

    def test_elim_poly(self):
        self.assertEqual(triangular_factorization(self.P.ideal([self.a^2*(self.a-1)^3*self.b^2*(self.c-3)^3,self.c^2-self.c, (self.a-2)^2*(self.b-1)^3]).groebner_basis()), [
                [self.a^2 - 4*self.a + 4, self.b, self.c],
                [self.a^5- 3*self.a^4+ 3*self.a^3-self.a^2, self.b-1, self.c],
                [self.a^2 - 4*self.a + 4, self.b, self.c-1],
                [self.a^5- 3*self.a^4+ 3*self.a^3-self.a^2, self.b-1, self.c-1],
                ])

    def test_variety_zero_dim(self):
        self.assertEqual(variety_zero_dim(self.P, [self.a^2-self.a]), {(1,), (0,)})
        self.assertEqual(variety_zero_dim(self.P, [self.b^2-self.b]), {(1,), (0,)})
        self.assertEqual(variety_zero_dim(self.P, [self.a^2-self.a,self.b^2-self.b]), {(1,1), (0,1), (1,0), (0,0)})
        self.assertEqual(variety_zero_dim(self.P, [self.a^2-self.a,self.b^2-self.b,self.a-self.b]), {(1,1), (0,0)})
        self.assertEqual(variety_zero_dim(self.P, [self.a^2-self.a,self.b^2-self.b,2*self.a-self.b]), {(0,0)})

    def test_variety_elem(self):
        self.assertEqual(variety_elem(self.P, [self.a, self.b-1]), {'a': 0, 'b': 1})
        self.assertEqual(variety_elem(self.P, [self.a, self.b-1, -1*self.c-3]), {'a': 0, 'b': 1, 'c': -3})
        self.assertEqual(variety_elem(self.P, [self.a, self.a*self.b-1]), None)
        self.check_variety_elem([self.a*self.b-1])
        self.check_variety_elem([self.a*self.b+self.a-1])
        self.check_variety_elem([self.a*self.b+self.a-1, self.c-4])

    def check_variety_elem(self, polys):
        root = variety_elem(self.P, polys)
        self.assertNotEqual(root, None)
        for p in polys:
            self.assertEqual(p(**root), 0)

    def test_parse_poly(self):
        self.assertEqual(parse_poly('f3^2 -f3'), [(1, [('f3', 2)]), (-1, [('f3', 1)])])
        self.assertEqual(parse_poly('-sum +f3 +f2 +f1 +f0'),
                [(-1, [('sum', 1)]),
                 (1, [('f3', 1)]),
                 (1, [('f2', 1)]),
                 (1, [('f1', 1)]),
                 (1, [('f0', 1)]),
                 ])
        self.assertEqual(parse_poly('-d2 +2*d1 +d0 -sum'),
                [(-1, [('d2', 1)]),
                 (2, [('d1', 1)]),
                 (1, [('d0', 1)]),
                 (-1, [('sum', 1)]),
                 ])
        self.assertEqual(parse_poly('d0^2 -d0'),
                [(1, [('d0', 2)]),
                 (-1, [('d0', 1)]),
                 ])
        self.assertEqual(parse_poly('d1^2 -d1'),
                [(1, [('d1', 2)]),
                 (-1, [('d1', 1)]),
                 ])
        self.assertEqual(parse_poly('d2^2 -d2'),
                [(1, [('d2', 2)]),
                 (-1, [('d2', 1)]),
                 ])
        self.assertEqual(parse_poly('f0*inv_witness[0] -1'),
                [(1, [('f0', 1), ('invEUwitnessEO0EC', 1)]),
                 (-1, []),
                 ])
        self.assertEqual(parse_poly('d0*inv_witness[1] -1'),
                [(1, [('d0', 1), ('invEUwitnessEO1EC', 1)]),
                 (-1, []),
                 ])
        self.assertEqual(parse_poly('f3*inv_witness[2] -1'),
                [(1, [('f3', 1), ('invEUwitnessEO2EC', 1)]),
                 (-1, []),
                 ])

PROBLEM_FORMAT = """

problem format:
  size: NNNNN
  variables: XX0 XX1 XX2
  polynomial: XX0*XX1^NNN +XX2 (CoCoA output format)

polynomial grammar:
  a *variable* meets [^*\^0-9][^*\^]*
  a *variable power* is a variable or a variable followed by ^ and an integer
  a *monomial* may start with +,-, may then have an integer, and then a *-separated list of variable powers
  a *polynomial* is a ' '-separated list of monomials

example:
  size: 5
  variables: f0 f1
  polynomial: f0^2 -f0
  polynomial: f1^2 -f1
  polynomial: f1 -f0
  polynomial: f1 -1

output:
  f0 1
  f1 1
"""

def name_san(s: str) -> str:
    """ Sanitize a name from CoCoA (which may include _ and brackets) into a sage-friendly name

    Rewrites:
      [ -> EO  (escape open)
      ] -> EC  (escape close)
      _ -> EU  (escape underscore)
      E -> EE  (escape escape)
    """
    return s.replace('E', 'EE').replace('_', 'EU').replace('[', 'EO').replace(']', 'EC')

def name_unsan(s: str) -> str:
    """ Undo sanitization. See `name_san`. """
    o = ""
    while s:
        if s[:2] == "EE":
            o += "E"
            s = s[2:]
        elif s[:2] == "EU":
            o += "_"
            s = s[2:]
        elif s[:2] == "EO":
            o += "["
            s = s[2:]
        elif s[:2] == "EC":
            o += "]"
            s = s[2:]
        else:
            o += s[0]
            s = s[1:]
    return o

def parse_monomial(s: str) -> Tuple[int, List[Tuple[str, int]]]:
    s = s.strip()
    const = -1 if s[0] == '-' else 1
    s = s.lstrip('-+')
    toks = s.split('*')
    assert len(toks) > 0
    if toks[0][0] in string.digits:
        const *= int(toks[0])
        toks = toks[1:]
    pps = []
    for t in toks:
        tt = t.split('^')
        if len(tt) == 1:
            pps.append((name_san(tt[0]), 1))
        elif len(tt) == 2:
            pps.append((name_san(tt[0]), int(tt[1])))
        else:
            assert False
    return (const, pps)

def parse_poly(s: str) -> List[Tuple[int, List[Tuple[str, int]]]]:
    return list(map(parse_monomial, s.strip().split()))

def build_poly(F, R, variables, poly: List[Tuple[int, List[Tuple[str, int]]]]):
    return sum(build_mon(F, R, variables, m) for m in poly)

def build_mon(F, R, variables, mon: Tuple[int, List[Tuple[str, int]]]):
    return (F.zero() + mon[0]) * product(variables[v] ^ p for v, p in mon[1])


def parse_problem(s: str):
    lines = [l.strip().split(': ') for l in s.strip().split('\n')]
    assert lines[0][0] == 'size'
    assert lines[1][0] == 'variables'
    F = GF(int(lines[0][1]))
    vs = list(map(name_san, lines[1][1].split()))
    R = PolynomialRing(F, vs)
    variables = { vs[i]: R.gen(i) for i in range(len(vs)) }
    ps = []
    for l in lines[2:]:
        assert l[0] == 'polynomial'
        p = parse_poly(l[1])
        pp = build_poly(F, R, variables, p)
        ps.append(pp)
    return (F, R, vs, ps)

def main():
    p = argparse.ArgumentParser(
            description="find common roots for a polynomial",
            formatter_class=argparse.RawDescriptionHelpFormatter,
            epilog=PROBLEM_FORMAT)
    p.add_argument('-t', '--test', nargs="*", help="run test suite")
    p.add_argument('-i', '--input', help="input problem; format given below")
    p.add_argument('-o', '--output', help="output; format given below")
    args = p.parse_args([a for a in sys.argv if a != "--"][1:])
    if args.test is not None:
        unittest.main(argv=sys.argv[:1] + args.test)
    else:
        with open(args.input) as f:
            F, R, vs, ps = parse_problem(f.read())
        solution = variety_elem(R, ps)
        with open(args.output, 'w') as f:
            if solution is not None:
                for v in vs:
                    f.write(f"{name_unsan(v)} {solution[v]}\n")


if __name__ == "__main__":
    main()
