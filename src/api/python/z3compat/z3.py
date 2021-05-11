############################################
# Copyright (c) 2021 The CVC5 Developers
#               2012 The Microsoft Corporation
#
# CVC5's Z3-based Python interface
#
# Author: Alex Ozdemir (aozdemir)
# pyz3 Author: Leonardo de Moura (leonardo)
############################################

"""
CVC5 is an SMT solver.

This is its Z3-based (and---as much as possible---Z3-compatible) python interface.

Several online tutorials for Z3Py are available at:
http://rise4fun.com/Z3Py/tutorial/guide

Please send feedback, comments and/or corrections on the Issue tracker for https://github.com/CVC5/CVC5.git.
Your comments are very valuable.

Small example:

>>> x = Int('x')
>>> y = Int('y')
>>> s = Solver()
>>> s.add(x > 0)
>>> s.add(x < 2)
>>> s.add(y == x + 1)
>>> s.check()
sat
>>> m = s.model()
>>> m[x]
1
>>> m[y]
2

Z3 exceptions:

>>> try:
...   x = BitVec('x', 32)
...   y = Bool('y')
...   # the expression x + y is type incorrect
...   n = x + y
... except Z3Exception as ex:
...   print("failed: %s" % ex)
failed: sort mismatch


TODO:
    * multiple solvers
    * FP
    * DT
    * quantifiers & variables
"""
from .z3printer import *
from fractions import Fraction
from decimal import Decimal
import decimal
import sys
import io
import math
import copy
import functools as ft
import operator as op

import pycvc5 as pc
from pycvc5 import kinds

DEBUG = __debug__


def debugging():
    global DEBUG
    return DEBUG


if sys.version < "3":

    def _is_int(v):
        return isinstance(v, (int, long))


else:

    def _is_int(v):
        return isinstance(v, int)


def enable_trace(msg):
    unimplemented()


def disable_trace(msg):
    unimplemented()


def unimplemented(msg=None):
    if msg is None:
        raise Exception("Unimplemented")
    else:
        raise Exception("Unimplemented: {}".format(msg))


def get_version_string():
    unimplemented()


def get_version():
    unimplemented()


def get_full_version():
    unimplemented()


class Z3Exception(Exception):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return str(self.value)


# We use _assert instead of the assert command because we want to
# produce nice error messages in Z3Py at rise4fun.com
def _assert(cond, msg):
    if not cond:
        raise Z3Exception(msg)


def open_log(fname):
    """Log interaction to a file. This function must be invoked immediately after init()."""
    unimplemented()


def append_log(s):
    """Append user-defined string to interaction log."""
    unimplemented()


# Hack for having nary functions that can receive one argument that is the
# list of arguments.
# Use this when function takes a single list of arguments
def _get_args(args):
    try:
        if len(args) == 1 and (isinstance(args[0], tuple) or isinstance(args[0], list)):
            return list(args[0])
        else:
            return list(args)
    except:  # len is not necessarily defined when args is not a sequence (use reflection?)
        return list(args)


# Use this when function takes multiple arguments
def _get_args_ast_list(args):
    try:
        if isinstance(args, set) or isinstance(args, tuple):
            return [arg for arg in args]
        else:
            return args
    except:
        return args


def _to_param_value(val):
    if isinstance(val, bool):
        if val == True:
            return "true"
        else:
            return "false"
    else:
        return str(val)


class Context(object):
    """A Context manages all other Z3 objects, global configuration options, etc.

    Z3Py uses a default global context. For most applications this is sufficient.
    An application may use multiple Z3 contexts. Objects created in one context
    cannot be used in another one. However, several objects may be "translated" from
    one context to another. It is not safe to access Z3 objects from multiple threads.
    The only exception is the method `interrupt()` that can be used to interrupt() a long
    computation.
    The initialization method receives global configuration options for the new context.
    """

    def __init__(self, *args, **kws):
        self.solver = pc.Solver()
        # self.solver.setOption("produce-assertions", "true")
        self.solver.setOption("produce-models", "true")
        self.vars = {}
        self.next_fresh_var = 0

    def __del__(self):
        self.solver = None

    def get_var(self, name, sort):
        """Get the variable identified by `name`.

        If no variable of that name (with that sort) has been created, creates one.

        Returns a Term
        """
        if (name, sort) not in self.vars:
            self.vars[(name, sort)] = self.solver.mkConst(sort.ast, name)
        return self.vars[(name, sort)]

    def next_fresh(self, sort, prefix):
        name = "{}{}".format(prefix, self.next_fresh_var)
        while (name, sort) in self.vars:
            self.next_fresh_var += 1
            name = "{}{}".format(prefix, self.next_fresh_var)
        return name

    def ref(self):
        """Return a reference to the actual C pointer to the Z3 context."""
        return self.solver

    def interrupt(self):
        """Interrupt a solver performing a satisfiability test, a tactic processing a goal, or simplify functions.

        This method can be invoked from a thread different from the one executing the
        interruptible procedure.
        """
        unimplemented()

    def __eq__(self, o):
        return self.solver == o.solver


# Global Z3 context
_main_ctx = None


def main_ctx():
    """Return a reference to the global Z3 context.

    >>> x = Real('x')
    >>> x.ctx == main_ctx()
    True
    >>> c = Context()
    >>> c == main_ctx()
    False
    >>> x2 = Real('x', c)
    >>> x2.ctx == c
    True
    >>> eq(x, x2)
    False
    """
    global _main_ctx
    if _main_ctx is None:
        _main_ctx = Context()
    return _main_ctx


def _get_ctx(ctx):
    if ctx is None:
        return main_ctx()
    else:
        return ctx


def get_ctx(ctx):
    return _get_ctx(ctx)


#########################################
#
# Term base class
#
#########################################


class ExprRef(object):
    """Constraints, formulas and terms are expressions in Z3.

    Expressions are ASTs. Every expression has a sort.
    There are three main kinds of expressions:
    function applications, quantifiers and bounded variables.
    A constant is a function application with 0 arguments.
    For quantifier free problems, all expressions are
    function applications.
    """

    def __init__(self, ast, ctx=None, reverse_children=False):
        self.ast = ast
        self.ctx = _get_ctx(ctx)
        self.reverse_children = reverse_children
        assert isinstance(self.ast, pc.Term)
        assert isinstance(self.ctx, Context)

    def __del__(self):
        if self.ctx is not None and self.ast is not None:
            self.ctx = None
            self.ast = None

    def __deepcopy__(self, memo={}):
        unimplemented()

    def __str__(self):
        return obj_to_string(self)

    def __repr__(self):
        return obj_to_string(self)

    def __hash__(self):
        return pc.TermHashFunction()(self.ast)

    def __nonzero__(self):
        return self.__bool__()

    def __bool__(self):
        if is_true(self):
            return True
        elif is_false(self):
            return False
        elif is_eq(self) and self.num_args() == 2:
            return self.arg(0).eq(self.arg(1))
        else:
            raise Z3Exception(
                "Symbolic expressions cannot be cast to concrete Boolean values."
            )

    def sexpr(self):
        """Return a string representing the AST node in s-expression notation.

        >>> x = Int('x')
        >>> ((x + 1)*x).sexpr()
        '(* (+ x 1) x)'
        """
        return str(self.ast)

    def as_ast(self):
        """Return a pointer to the underlying Term object."""
        return self.ast

    def get_id(self):
        """Return unique identifier for object. It can be used for hash-tables and maps."""
        return self.ast.getId()

    def ctx_ref(self):
        """Return a reference to the C context where this AST node is stored."""
        return self.ctx

    def eq(self, other):
        """Return `True` if `self` and `other` are structurally identical.

        >>> x = Int('x')
        >>> n1 = x + 1
        >>> n2 = 1 + x
        >>> n1.eq(n2)
        False
        """
        if debugging():
            _assert(is_ast(other), "Z3 AST expected")
        return self.ctx_ref() == other.ctx_ref() and self.as_ast() == other.as_ast()

    def hash(self):
        """Return a hashcode for the `self`.

        >>> n1 = Int('x') + 1
        >>> n2 = Int('x') + 1
        >>> n1.hash() == n2.hash()
        True
        """
        return self.as_ast().__hash__()

    def sort(self):
        """Return the sort of expression `self`.

        >>> x = Int('x')
        >>> (x + 1).sort()
        Int
        >>> y = Real('y')
        >>> (x + y).sort()
        Real
        """
        return _sort(self.ctx, self.ast)

    def __eq__(self, other):
        """Return a Z3 expression that represents the constraint `self == other`.

        If `other` is `None`, then this method simply returns `False`.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> a == b
        a == b
        >>> a is None
        False
        """
        if other is None:
            return False
        a, b = _coerce_exprs(self, other)
        c = self.ctx_ref()
        return BoolRef(c.solver.mkTerm(kinds.Equal, a.as_ast(), b.as_ast()), c)

    def __hash__(self):
        """Hash code."""
        return self.ast.__hash__()

    def __ne__(self, other):
        """Return a Z3 expression that represents the constraint `self != other`.

        If `other` is `None`, then this method simply returns `True`.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> a != b
        a != b
        >>> a is not None
        True
        """
        if other is None:
            return True
        a, b = _coerce_exprs(self, other)
        c = self.ctx_ref()
        return BoolRef(c.solver.mkTerm(kinds.Distinct, a.as_ast(), b.as_ast()), c)

    def params(self):
        return self.decl().params()

    def decl(self):
        """Return the Z3 function declaration associated with a Z3 application.

        >>> f = Function('f', IntSort(), IntSort())
        >>> a = Int('a')
        >>> t = f(a)
        >>> eq(t.decl(), f)
        True
        """
        if is_app_of(self, kinds.ApplyUf):
            return _to_expr_ref(list(self.ast)[0], self.ctx)
        else:
            unimplemented("Declarations for non-function applications")

    def kind(self):
        """Return the kinds of this term

        >>> f = Function('f', IntSort(), IntSort())
        >>> a = Int('a')
        >>> t = f(a)
        >>> t.kind() == kinds.ApplyUf
        True
        """
        return self.ast.getKind()

    def num_args(self):
        """Return the number of arguments of a Z3 application.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> (a + b).num_args()
        2
        >>> f = Function('f', IntSort(), IntSort(), IntSort(), IntSort())
        >>> t = f(a, b, 0)
        >>> t.num_args()
        3
        """
        if debugging():
            _assert(is_app(self), "Z3 application expected")
        if is_app_of(self, kinds.ApplyUf):
            return len(list(self.as_ast())) - 1
        else:
            return len(list(self.as_ast()))

    def arg(self, idx):
        """Return argument `idx` of the application `self`.

        This method assumes that `self` is a function application with at least `idx+1` arguments.

        >>> a = Int('a')
        >>> b = Int('b')
        >>> f = Function('f', IntSort(), IntSort(), IntSort(), IntSort())
        >>> t = f(a, b, 0)
        >>> t.arg(0)
        a
        >>> t.arg(1)
        b
        >>> t.arg(2)
        0
        """
        if debugging():
            _assert(is_app(self), "Z3 application expected")
            _assert(idx < self.num_args(), "Invalid argument index")
        if is_app_of(self, kinds.ApplyUf):
            return _to_expr_ref(self.as_ast()[idx + 1], self.ctx_ref())
        elif self.reverse_children:
            return _to_expr_ref(
                self.as_ast()[self.num_args() - (idx + 1)], self.ctx_ref()
            )
        else:
            return _to_expr_ref(self.as_ast()[idx], self.ctx_ref())

    def children(self):
        """Return a list containing the children of the given expression

        >>> a = Int('a')
        >>> b = Int('b')
        >>> f = Function('f', IntSort(), IntSort(), IntSort(), IntSort())
        >>> t = f(a, b, 0)
        >>> t.children()
        [a, b, 0]
        """
        if is_app_of(self, kinds.ApplyUf):
            return [_to_expr_ref(a, self.ctx) for a in list(self.ast)[1:]]
        else:
            if is_app(self):
                args = list(self.ast)
                if self.reverse_children:
                    args = reversed(args)
                return [_to_expr_ref(a, self.ctx) for a in args]
            else:
                return []


def is_ast(a):
    """Return `True` if `a` is an AST node.

    >>> is_ast(10)
    False
    >>> is_ast(IntVal(10))
    True
    >>> is_ast(Int('x'))
    True
    >>> is_ast(BoolSort())
    True
    >>> is_ast(Function('f', IntSort(), IntSort()))
    True
    >>> is_ast("x")
    False
    >>> is_ast(Solver())
    False
    """
    return isinstance(a, (ExprRef, SortRef))


def eq(a, b):
    """Return `True` if `a` and `b` are structurally identical AST nodes.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> eq(x, y)
    False
    >>> eq(x + 1, x + 1)
    True
    >>> eq(x + 1, 1 + x)
    False
    """
    if debugging():
        _assert(is_ast(a) and is_ast(b), "Z3 ASTs expected")
    return a.eq(b)


def _ctx_from_ast_arg_list(args, default_ctx=None):
    ctx = None
    for a in args:
        if is_ast(a):
            if ctx is None:
                ctx = a.ctx
            else:
                if debugging():
                    _assert(ctx == a.ctx, "Context mismatch")
    if ctx is None:
        ctx = default_ctx
    return ctx


def _ctx_from_ast_args(*args):
    return _ctx_from_ast_arg_list(args)


#########################################
#
# Sorts
#
#########################################


class SortRef(object):
    """A Sort is essentially a type. Every Z3 expression has a sort. A sort is an AST node."""

    def __init__(self, ast, ctx=None):
        self.ast = ast
        self.ctx = _get_ctx(ctx)
        assert isinstance(self.ast, pc.Sort)
        assert isinstance(self.ctx, Context)

    def __del__(self):
        if self.ctx is not None:
            self.ctx = None
        if self.ast is not None:
            self.ast = None

    def __deepcopy__(self, memo={}):
        unimplemented()

    def __str__(self):
        return obj_to_string(self)

    def __repr__(self):
        return obj_to_string(self)

    def __eq__(self, other):
        return self.ast == other.ast

    def __hash__(self):
        return self.ast.__hash__()

    def sexpr(self):
        """Return a string representing the AST node in s-expression notation.

        >>> x = Int('x')
        >>> ((x + 1)*x).sexpr()
        '(* (+ x 1) x)'
        """
        return str(self.ast)

    def as_ast(self):
        """Return a pointer to the underlying Sort object."""
        return self.ast

    def ctx_ref(self):
        """Return a reference to the C context where this AST node is stored."""
        return self.ctx

    def eq(self, other):
        """Return `True` if `self` and `other` are structurally identical.

        >>> x = Int('x')
        >>> n1 = x + 1
        >>> n2 = 1 + x
        >>> n1.eq(n2)
        False
        >>> n1.eq(x + 1)
        True
        """
        instance_check(other, SortRef)
        assert self.ctx_ref() == other.ctx_ref()
        return self.as_ast() == other.as_ast()

    def hash(self):
        """Return a hashcode for the `self`.

        >>> n1 = Int('x') + 1
        >>> n2 = Int('x') + 1
        >>> n1.hash() == n2.hash()
        True
        """
        return self.as_ast().__hash__()

    def subsort(self, other):
        """Return `True` if `self` is a subsort of `other`.

        >>> IntSort().subsort(RealSort())
        True
        """
        return False

    def cast(self, val):
        """Try to cast `val` as an element of sort `self`.

        This method is used in Z3Py to convert Python objects such as integers,
        floats, longs and strings into Z3 expressions.

        >>> x = Int('x')
        >>> RealSort().cast(x)
        ToReal(x)
        """
        if debugging():
            _assert(is_expr(val), "Z3 expression expected")
            _assert(self.eq(val.sort()), "Sort mismatch")
        return val

    def name(self):
        """Return the name (string) of sort `self`.

        >>> BoolSort().name()
        'Bool'
        >>> ArraySort(IntSort(), IntSort()).name()
        '(Array Int Int)'
        """
        return str(self.ast)

    def __ne__(self, other):
        """Return `True` if `self` and `other` are not the same Z3 sort.

        >>> p = Bool('p')
        >>> p.sort() != BoolSort()
        False
        >>> p.sort() != IntSort()
        True
        """
        return self.ast != other.ast

    def __hash__(self):
        """Hash code."""
        return self.ast.__hash__()


def is_sort(s):
    """Return `True` if `s` is a Z3 sort.

    >>> is_sort(IntSort())
    True
    >>> is_sort(Int('x'))
    False
    >>> is_expr(Int('x'))
    True
    """
    return isinstance(s, SortRef)


def instance_check(item, instance):
    _assert(
        isinstance(item, instance),
        "Expected {}, but got a {}".format(instance, type(item)),
    )


def _to_sort_ref(s, ctx):
    if isinstance(s, SortRef):
        s = s.ast
    if debugging():
        instance_check(s, pc.Sort)
    if s.isBoolean():
        return BoolSortRef(s, ctx)
    elif s.isInteger() or s.isReal():
        return ArithSortRef(s, ctx)
    elif s.isBitVector():
        return BitVecSortRef(s, ctx)
    elif s.isArray():
        return ArraySortRef(s, ctx)
    elif s.isSet():
        return SetSortRef(s, ctx)
    elif s.isDatatype():
        return DatatypeSortRef(s, ctx)
    return SortRef(s, ctx)


def _sort(ctx, a):
    if isinstance(a, ExprRef):
        a = a.ast
    instance_check(a, pc.Term)
    return _to_sort_ref(a.getSort(), ctx)


def DeclareSort(name, ctx=None):
    """Create a new uninterpreted sort named `name`.

    If `ctx=None`, then the new sort is declared in the global Z3Py context.

    >>> A = DeclareSort('A')
    >>> a = Const('a', A)
    >>> b = Const('b', A)
    >>> a.sort() == A
    True
    >>> b.sort() == A
    True
    >>> a == b
    a == b
    """
    ctx = _get_ctx(ctx)
    return SortRef(ctx.solver.mkUninterpretedSort(name), ctx)


#########################################
#
# Function Declarations
#
#########################################


class FuncDeclRef(ExprRef):
    """Function declaration. Every constant and function have an associated declaration.

    The declaration assigns a name, a sort (i.e., type), and for function
    the sort (i.e., type) of each of its arguments. Note that, in Z3,
    a constant is a function with 0 arguments.
    """

    def as_func_decl(self):
        return self.ast

    def name(self):
        """Return the name of the function declaration `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> f.name()
        'f'
        >>> isinstance(f.name(), str)
        True
        """
        return str(self)

    def arity(self):
        """Return the number of arguments of a function declaration. If `self` is a constant, then `self.arity()` is 0.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> f.arity()
        2
        """
        return self.ast.getSort().getFunctionArity()

    def domain(self, i):
        """Return the sort of the argument `i` of a function declaration. This method assumes that `0 <= i < self.arity()`.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> f.domain(0)
        Int
        >>> f.domain(1)
        Real
        """
        return _to_sort_ref(
            self.ast.getSort().getFunctionDomainSorts()[i], self.ctx_ref()
        )

    def range(self):
        """Return the sort of the range of a function declaration. For constants, this is the sort of the constant.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> f.range()
        Bool
        """
        return SortRef(self.ast.getSort().getFunctionCodomainSort(), self.ctx_ref())

    def __call__(self, *args):
        """Create a Z3 application expression using the function `self`, and the given arguments.

        The arguments must be Z3 expressions. This method assumes that
        the sorts of the elements in `args` match the sorts of the
        domain. Limited coercion is supported.  For example, if
        args[0] is a Python integer, and the function expects a Z3
        integer, then the argument is automatically converted into a
        Z3 integer.

        >>> f = Function('f', IntSort(), RealSort(), BoolSort())
        >>> x = Int('x')
        >>> y = Real('y')
        >>> f(x, y)
        f(x, y)
        >>> f(x, x)
        f(x, ToReal(x))
        """
        args = _get_args(args)
        num = len(args)
        if debugging():
            _assert(
                num == self.arity(), "Incorrect number of arguments to %s" % self
            )
        _args = []
        saved = []
        for i in range(num):
            # self.domain(i).cast(args[i]) may create a new Z3 expression,
            # then we must save in 'saved' to prevent it from being garbage collected.
            tmp = self.domain(i).cast(args[i])
            saved.append(tmp)
            _args.append(tmp.as_ast())
        return _to_expr_ref(
            self.ctx.solver.mkTerm(kinds.ApplyUf, self.ast, *_args), self.ctx
        )


def is_func_decl(a):
    """Return `True` if `a` is a Z3 function declaration.

    >>> f = Function('f', IntSort(), IntSort())
    >>> is_func_decl(f)
    True
    >>> x = Real('x')
    >>> is_func_decl(x)
    False
    """
    return isinstance(a, FuncDeclRef)


def Function(name, *sig):
    """Create a new Z3 uninterpreted function with the given sorts.

    >>> f = Function('f', IntSort(), IntSort())
    >>> f(f(0))
    f(f(0))
    """
    sig = _get_args(sig)
    if debugging():
        _assert(len(sig) > 0, "At least two arguments expected")
    arity = len(sig) - 1
    rng = sig[arity]
    if debugging():
        _assert(is_sort(rng), "Z3 sort expected")
    ctx = rng.ctx
    sort = ctx.solver.mkFunctionSort([sig[i].ast for i in range(arity)], rng.ast)
    e = ctx.get_var(name, _to_sort_ref(sort, ctx))
    return FuncDeclRef(e, ctx)


def FreshFunction(*sig):
    """Create a new fresh Z3 uninterpreted function with the given sorts."""
    sig = _get_args(sig)
    if debugging():
        _assert(len(sig) > 0, "At least two arguments expected")
    arity = len(sig) - 1
    rng = sig[arity]
    if debugging():
        _assert(is_sort(rng), "Z3 sort expected")
    ctx = rng.ctx
    sort = ctx.solver.mkFunctionSort([sig[i].ast for i in range(arity)], rng.ast)
    name = ctx.next_fresh(sort, "freshfn")
    return Function(name, *sig)


def _to_func_decl_ref(a, ctx):
    return FuncDeclRef(a, ctx)


#########################################
#
# Expressions
#
#########################################


def _to_expr_ref(a, ctx, r=None):
    if isinstance(a, ExprRef):
        ast = a.ast
        if r is None:
            r = a.reverse_children
    elif isinstance(a, pc.Term):
        if r is None:
            r = False
        ast = a
    sort = ast.getSort()
    if sort.isBoolean():
        return BoolRef(ast, ctx, r)
    if sort.isInteger():
        if ast.getKind() == kinds.ConstRational:
            return IntNumRef(ast, ctx, r)
        return ArithRef(ast, ctx, r)
    if sort.isReal():
        if ast.getKind() == kinds.ConstRational:
            return RatNumRef(ast, ctx, r)
        return ArithRef(ast, ctx, r)
    if sort.isBitVector():
        if ast.getKind() == kinds.ConstBV:
            return BitVecNumRef(ast, ctx, r)
        else:
            return BitVecRef(ast, ctx, r)
    if sort.isArray():
        return ArrayRef(ast, ctx, r)
    if sort.isSet():
        return SetRef(ast, ctx, r)
    if sort.isDatatype():
        return DatatypeRef(ast, ctx, r)
    return ExprRef(ast, ctx, r)


def _coerce_expr_merge(s, a):
    if is_expr(a):
        s1 = a.sort()
        if s is None:
            return s1
        if s1.eq(s):
            return s
        elif s.subsort(s1):
            return s1
        elif s1.subsort(s):
            return s
        else:
            if debugging():
                _assert(s1.ctx == s.ctx, "context mismatch")
                _assert(False, "sort mismatch")
    else:
        return s


def _coerce_exprs(a, b, ctx=None):
    if not is_expr(a) and not is_expr(b):
        a = _py2expr(a, ctx)
        b = _py2expr(b, ctx)
    s = None
    s = _coerce_expr_merge(s, a)
    s = _coerce_expr_merge(s, b)
    a = s.cast(a)
    b = s.cast(b)
    return (a, b)


def _reduce(f, l, a):
    r = a
    for e in l:
        r = f(r, e)
    return r


def _coerce_expr_list(alist, ctx=None):
    has_expr = False
    for a in alist:
        if is_expr(a):
            has_expr = True
            break
    if not has_expr:
        alist = [_py2expr(a, ctx) for a in alist]
    s = _reduce(_coerce_expr_merge, alist, None)
    return [s.cast(a) for a in alist]


def is_expr(a):
    """Return `True` if `a` is a Z3 expression.

    >>> a = Int('a')
    >>> is_expr(a)
    True
    >>> is_expr(a + 1)
    True
    >>> is_expr(IntSort())
    False
    >>> is_expr(1)
    False
    >>> is_expr(IntVal(1))
    True
    >>> x = Int('x')
    """
    return isinstance(a, ExprRef)


def is_app(a):
    """Return `True` if `a` is a Z3 function application.

    Note that, constants are function applications with 0 arguments.

    >>> a = Int('a')
    >>> is_app(a)
    True
    >>> is_app(a + 1)
    True
    >>> is_app(IntSort())
    False
    >>> is_app(1)
    False
    >>> is_app(IntVal(1))
    True
    >>> x = Int('x')
    """
    if not isinstance(a, ExprRef):
        return False
    else:
        return True


def is_const(a):
    """Return `True` if `a` is Z3 constant/variable expression.

    >>> a = Int('a')
    >>> is_const(a)
    True
    >>> is_const(a + 1)
    False
    >>> is_const(1)
    False
    >>> is_const(IntVal(1))
    True
    >>> x = Int('x')
    """
    return is_expr(a) and a.ast.getKind() in [
        kinds.ConstBoolean,
        kinds.ConstBV,
        kinds.ConstFP,
        kinds.ConstRational,
        kinds.Emptyset,
        kinds.UniverseSet,
        kinds.Constant,
    ]


def is_var(a):
    """Return `True` if `a` is variable.

    Z3 uses de-Bruijn indices for representing bound variables in
    quantifiers.

    >>> x = Int('x')
    >>> is_var(x)
    False
    >>> is_const(x)
    True
    """
    if not is_expr(a):
        return False
    k = a.ast.getKind()
    return k == kinds.Variable


def is_app_of(a, k):
    """Return `True` if `a` is an application of the given kind `k`.

    >>> x = Int('x')
    >>> n = x + 1
    >>> is_app_of(n, kinds.Plus)
    True
    >>> is_app_of(n, kinds.Mult)
    False
    """
    return is_expr(a) and a.ast.getKind() == k


def If(a, b, c, ctx=None):
    """Create a Z3 if-then-else expression.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> max = If(x > y, x, y)
    >>> max
    If(x > y, x, y)
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a, b, c], ctx))
    s = BoolSort(ctx)
    a = s.cast(a)
    b, c = _coerce_exprs(b, c, ctx)
    if debugging():
        _assert(a.ctx == b.ctx, "Context mismatch")
    return _to_expr_ref(ctx.solver.mkTerm(kinds.Ite, a.ast, b.ast, c.ast), ctx)


def Distinct(*args):
    """Create a Z3 distinct expression.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> Distinct(x, y)
    x != y
    >>> z = Int('z')
    >>> Distinct(x, y, z)
    Distinct(x, y, z)
    """
    args = _get_args(args)
    ctx = _ctx_from_ast_arg_list(args)
    if debugging():
        _assert(
            ctx is not None, "At least one of the arguments must be a Z3 expression"
        )
    args = _coerce_expr_list(args, ctx)
    return BoolRef(ctx.solver.mkTerm(kinds.Distinct, *[a.ast for a in args]), ctx)


def _mk_bin(f, a, b):
    args = (Ast * 2)()
    if debugging():
        _assert(a.ctx == b.ctx, "Context mismatch")
    args[0] = a.as_ast()
    args[1] = b.as_ast()
    return f(a.ctx.ref(), 2, args)


def Const(name, sort):
    """Create a constant of the given sort.

    >>> Const('x', IntSort())
    x
    """
    if debugging():
        _assert(isinstance(sort, SortRef), "Z3 sort expected")
    ctx = sort.ctx
    e = ctx.get_var(name, sort)
    return _to_expr_ref(e, ctx)


def Consts(names, sort):
    """Create several constants of the given sort.

    `names` is a string containing the names of all constants to be created.
    Blank spaces separate the names of different constants.

    >>> x, y, z = Consts('x y z', IntSort())
    >>> x + y + z
    x + y + z
    """
    if isinstance(names, str):
        names = names.split(" ")
    return [Const(name, sort) for name in names]


def FreshConst(sort, prefix="c"):
    """Create a fresh constant of a specified sort"""
    ctx = sort.ctx
    name = ctx.next_fresh(sort, prefix)
    return Const(name, sort)


#########################################
#
# Booleans
#
#########################################


class BoolSortRef(SortRef):
    """Boolean sort."""

    def cast(self, val):
        """Try to cast `val` as a Boolean.

        >>> x = BoolSort().cast(True)
        >>> x
        True
        >>> is_expr(x)
        True
        >>> is_expr(True)
        False
        >>> x.sort()
        Bool
        """
        if isinstance(val, bool):
            return BoolVal(val, self.ctx)
        if debugging():
            if not is_expr(val):
                _assert(
                    is_expr(val),
                    "True, False or Z3 Boolean expression expected. Received %s of type %s"
                    % (val, type(val)),
                )
            if not self.eq(val.sort()):
                _assert(
                    self.eq(val.sort()),
                    "Value cannot be converted into a Z3 Boolean value",
                )
        return val

    def subsort(self, other):
        return isinstance(other, ArithSortRef)

    def is_int(self):
        return True

    def is_bool(self):
        return True


class BoolRef(ExprRef):
    """All Boolean expressions are instances of this class."""

    def sort(self):
        return _sort(self.ctx, self.ast)

    def __rmul__(self, other):
        return self * other

    def __mul__(self, other):
        """Create the Z3 expression `self * other`."""
        if other == 1:
            return self
        if other == 0:
            return 0
        return If(self, other, 0)


def is_bool(a):
    """Return `True` if `a` is a Z3 Boolean expression.

    >>> p = Bool('p')
    >>> is_bool(p)
    True
    >>> q = Bool('q')
    >>> is_bool(And(p, q))
    True
    >>> x = Real('x')
    >>> is_bool(x)
    False
    >>> is_bool(x == 0)
    True
    """
    return isinstance(a, BoolRef)


def is_true(a):
    """Return `True` if `a` is the Z3 true expression.

    >>> p = Bool('p')
    >>> is_true(p)
    False
    >>> x = Real('x')
    >>> is_true(x == 0)
    False
    >>> # True is a Python Boolean expression
    >>> is_true(True)
    False
    """
    return is_app_of(a, kinds.ConstBoolean) and a.ast == a.ctx.solver.mkTrue()


def is_false(a):
    """Return `True` if `a` is the Z3 false expression.

    >>> p = Bool('p')
    >>> is_false(p)
    False
    >>> is_false(False)
    False
    >>> is_false(BoolVal(False))
    True
    """
    return is_app_of(a, kinds.ConstBoolean) and a.ast == a.ctx.solver.mkFalse()


def is_and(a):
    """Return `True` if `a` is a Z3 and expression.

    >>> p, q = Bools('p q')
    >>> is_and(And(p, q))
    True
    >>> is_and(Or(p, q))
    False
    """
    return is_app_of(a, kinds.And)


def is_or(a):
    """Return `True` if `a` is a Z3 or expression.

    >>> p, q = Bools('p q')
    >>> is_or(Or(p, q))
    True
    >>> is_or(And(p, q))
    False
    """
    return is_app_of(a, kinds.Or)


def is_implies(a):
    """Return `True` if `a` is a Z3 implication expression.

    >>> p, q = Bools('p q')
    >>> is_implies(Implies(p, q))
    True
    >>> is_implies(And(p, q))
    False
    """
    return is_app_of(a, kinds.Implies)


def is_not(a):
    """Return `True` if `a` is a Z3 not expression.

    >>> p = Bool('p')
    >>> is_not(p)
    False
    >>> is_not(Not(p))
    True
    """
    return is_app_of(a, kinds.Not)


def is_eq(a):
    """Return `True` if `a` is a Z3 equality expression.

    >>> x, y = Ints('x y')
    >>> is_eq(x == y)
    True
    """
    return is_app_of(a, kinds.Equal)


def is_distinct(a):
    """Return `True` if `a` is a Z3 distinct expression.

    >>> x, y, z = Ints('x y z')
    >>> is_distinct(x == y)
    False
    >>> is_distinct(Distinct(x, y, z))
    True
    """
    return is_app_of(a, kinds.Distinct)


def BoolSort(ctx=None):
    """Return the Boolean Z3 sort. If `ctx=None`, then the global context is used.

    >>> BoolSort()
    Bool
    >>> p = Const('p', BoolSort())
    >>> is_bool(p)
    True
    >>> r = Function('r', IntSort(), IntSort(), BoolSort())
    >>> r(0, 1)
    r(0, 1)
    >>> is_bool(r(0, 1))
    True
    """
    ctx = _get_ctx(ctx)
    return BoolSortRef(ctx.solver.getBooleanSort(), ctx)


def BoolVal(val, ctx=None):
    """Return the Boolean value `True` or `False`. If `ctx=None`, then the global context is used.

    >>> BoolVal(True)
    True
    >>> is_true(BoolVal(True))
    True
    >>> is_true(True)
    False
    >>> is_false(BoolVal(False))
    True
    """
    ctx = _get_ctx(ctx)
    if val == False:
        return BoolRef(ctx.solver.mkFalse(), ctx)
    else:
        return BoolRef(ctx.solver.mkTrue(), ctx)


def Bool(name, ctx=None):
    """Return a Boolean constant named `name`. If `ctx=None`, then the global context is used.

    >>> p = Bool('p')
    >>> q = Bool('q')
    >>> And(p, q)
    And(p, q)
    """
    ctx = _get_ctx(ctx)
    e = ctx.get_var(name, BoolSort(ctx))
    return BoolRef(e, ctx)


def Bools(names, ctx=None):
    """Return a tuple of Boolean constants.

    `names` is a single string containing all names separated by blank spaces.
    If `ctx=None`, then the global context is used.

    >>> p, q, r = Bools('p q r')
    >>> And(p, Or(q, r))
    And(p, Or(q, r))
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [Bool(name, ctx) for name in names]


def BoolVector(prefix, sz, ctx=None):
    """Return a list of Boolean constants of size `sz`.

    The constants are named using the given prefix.
    If `ctx=None`, then the global context is used.

    >>> P = BoolVector('p', 3)
    >>> P
    [p__0, p__1, p__2]
    >>> And(P)
    And(p__0, p__1, p__2)
    """
    return [Bool("%s__%s" % (prefix, i)) for i in range(sz)]


def FreshBool(prefix="b", ctx=None):
    """Return a fresh Boolean constant in the given context using the given prefix.

    If `ctx=None`, then the global context is used.

    >>> b1 = FreshBool()
    >>> b2 = FreshBool()
    >>> eq(b1, b2)
    False
    """
    ctx = _get_ctx(ctx)
    sort = BoolSort(ctx)
    name = ctx.next_fresh(sort, prefix)
    return Bool(name, ctx)


def Implies(a, b, ctx=None):
    """Create a Z3 implies expression.

    >>> p, q = Bools('p q')
    >>> Implies(p, q)
    Implies(p, q)
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a, b], ctx))
    s = BoolSort(ctx)
    a = s.cast(a)
    b = s.cast(b)
    return BoolRef(ctx.solver.mkTerm(kinds.Implies, a.as_ast(), b.as_ast()), ctx)


def Xor(a, b, ctx=None):
    """Create a Z3 Xor expression.

    >>> p, q = Bools('p q')
    >>> Xor(p, q)
    Xor(p, q)
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a, b], ctx))
    s = BoolSort(ctx)
    a = s.cast(a)
    b = s.cast(b)
    return BoolRef(ctx.solver.mkTerm(kinds.Xor, a.as_ast(), b.as_ast()), ctx)


def Not(a, ctx=None):
    """Create a Z3 not expression or probe.

    >>> p = Bool('p')
    >>> Not(Not(p))
    Not(Not(p))
    """
    ctx = _get_ctx(_ctx_from_ast_arg_list([a], ctx))
    s = BoolSort(ctx)
    a = s.cast(a)
    return BoolRef(ctx.solver.mkTerm(kinds.Not, a.as_ast()), ctx)


def mk_not(a):
    if is_not(a):
        return a.arg(0)
    else:
        return Not(a)


def And(*args):
    """Create a Z3 and-expression or and-probe.

    >>> p, q, r = Bools('p q r')
    >>> And(p, q, r)
    And(p, q, r)
    >>> P = BoolVector('p', 5)
    >>> And(P)
    And(p__0, p__1, p__2, p__3, p__4)
    """
    last_arg = None
    if len(args) > 0:
        last_arg = args[len(args) - 1]
    if isinstance(last_arg, Context):
        ctx = args[len(args) - 1]
        args = args[: len(args) - 1]
    elif len(args) == 1 and (isinstance(args[0], list) or isinstance(args[0], tuple)):
        ctx = args[0][0]
        args = [a for a in args[0]]
    else:
        ctx = None
    args = _get_args(args)
    ctx = _get_ctx(_ctx_from_ast_arg_list(args, ctx))
    if debugging():
        _assert(
            ctx is not None,
            "At least one of the arguments must be a Z3 expression or probe",
        )
    args = _coerce_expr_list(args, ctx)
    return BoolRef(ctx.solver.mkTerm(kinds.And, *[a.ast for a in args]), ctx)


def Or(*args):
    """Create a Z3 or-expression or or-probe.

    >>> p, q, r = Bools('p q r')
    >>> Or(p, q, r)
    Or(p, q, r)
    >>> P = BoolVector('p', 5)
    >>> Or(P)
    Or(p__0, p__1, p__2, p__3, p__4)
    """
    last_arg = None
    if len(args) > 0:
        last_arg = args[len(args) - 1]
    if isinstance(last_arg, Context):
        ctx = args[len(args) - 1]
        args = args[: len(args) - 1]
    elif len(args) == 1 and (isinstance(args[0], list) or isinstance(args[0], tuple)):
        ctx = args[0][0]
        args = [a for a in args[0]]
    else:
        ctx = None
    args = _get_args(args)
    ctx = _get_ctx(_ctx_from_ast_arg_list(args, ctx))
    if debugging():
        _assert(
            ctx is not None,
            "At least one of the arguments must be a Z3 expression or probe",
        )
    args = _coerce_expr_list(args, ctx)
    return BoolRef(ctx.solver.mkTerm(kinds.Or, *[a.ast for a in args]), ctx)


#########################################
#
# Arithmetic
#
#########################################


class ArithSortRef(SortRef):
    """Real and Integer sorts."""

    def is_real(self):
        """Return `True` if `self` is of the sort Real.

        >>> x = Real('x')
        >>> x.is_real()
        True
        >>> (x + 1).is_real()
        True
        >>> x = Int('x')
        >>> x.is_real()
        False
        """
        return self.ast == self.ctx.solver.getRealSort()

    def is_int(self):
        """Return `True` if `self` is of the sort Integer.

        >>> x = Int('x')
        >>> x.is_int()
        True
        >>> (x + 1).is_int()
        True
        >>> x = Real('x')
        >>> x.is_int()
        False
        """
        return self.ast == self.ctx.solver.getIntegerSort()

    def subsort(self, other):
        """Return `True` if `self` is a subsort of `other`."""
        return self.is_int() and is_arith_sort(other) and other.is_real()

    def cast(self, val):
        """Try to cast `val` as an Integer or Real.

        >>> IntSort().cast(10)
        10
        >>> is_int(IntSort().cast(10))
        True
        >>> is_int(10)
        False
        >>> RealSort().cast(10)
        10
        >>> is_real(RealSort().cast(10))
        True
        """
        if is_expr(val):
            if debugging():
                _assert(self.ctx == val.ctx, "Context mismatch")
            val_s = val.sort()
            if self.eq(val_s):
                return val
            if val_s.is_int() and self.is_real():
                return ToReal(val)
            if val_s.is_bool() and self.is_int():
                return If(val, 1, 0)
            if val_s.is_bool() and self.is_real():
                return ToReal(If(val, 1, 0))
            if debugging():
                _assert(False, "Z3 Integer/Real expression expected")
        else:
            if self.is_int():
                return IntVal(val, self.ctx)
            if self.is_real():
                return RealVal(val, self.ctx)
            if debugging():
                _assert(
                    False,
                    "int, long, float, string (numeral), or Z3 Integer/Real expression expected. Got %s"
                    % self,
                )


def is_arith_sort(s):
    """Return `True` if s is an arithmetical sort (type).

    >>> is_arith_sort(IntSort())
    True
    >>> is_arith_sort(RealSort())
    True
    >>> is_arith_sort(BoolSort())
    False
    >>> n = Int('x') + 1
    >>> is_arith_sort(n.sort())
    True
    """
    return isinstance(s, ArithSortRef)


class ArithRef(ExprRef):
    """Integer and Real expressions."""

    def sort(self):
        """Return the sort (type) of the arithmetical expression `self`.

        >>> Int('x').sort()
        Int
        >>> (Real('x') + 1).sort()
        Real
        """
        return _sort(self.ctx, self.ast)

    def is_int(self):
        """Return `True` if `self` is an integer expression.

        >>> x = Int('x')
        >>> x.is_int()
        True
        >>> (x + 1).is_int()
        True
        >>> y = Real('y')
        >>> (x + y).is_int()
        False
        """
        return self.sort().is_int()

    def is_real(self):
        """Return `True` if `self` is an real expression.

        >>> x = Real('x')
        >>> x.is_real()
        True
        >>> (x + 1).is_real()
        True
        """
        return self.sort().is_real()

    def __add__(self, other):
        """Create the Z3 expression `self + other`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x + y
        x + y
        >>> (x + y).sort()
        Int
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Plus, a.ast, b.ast), self.ctx)

    def __radd__(self, other):
        """Create the Z3 expression `other + self`.

        >>> x = Int('x')
        >>> 10 + x
        10 + x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Plus, b.ast, a.ast), self.ctx)

    def __mul__(self, other):
        """Create the Z3 expression `self * other`.

        >>> x = Real('x')
        >>> y = Real('y')
        >>> x * y
        x*y
        >>> (x * y).sort()
        Real
        """
        if isinstance(other, BoolRef):
            return If(other, self, 0)
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Mult, a.ast, b.ast), self.ctx)

    def __rmul__(self, other):
        """Create the Z3 expression `other * self`.

        >>> x = Real('x')
        >>> 10 * x
        10*x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Mult, b.ast, a.ast), self.ctx)

    def __sub__(self, other):
        """Create the Z3 expression `self - other`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x - y
        x - y
        >>> (x - y).sort()
        Int
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Minus, a.ast, b.ast), self.ctx)

    def __rsub__(self, other):
        """Create the Z3 expression `other - self`.

        >>> x = Int('x')
        >>> 10 - x
        10 - x
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Minus, b.ast, a.ast), self.ctx)

    def __pow__(self, other):
        """Create the Z3 expression `self**other` (** is the power operator).

        >>> x = Real('x')
        >>> x**3
        x**3
        >>> (x**3).sort()
        Real
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Pow, a.ast, b.ast), self.ctx)

    def __rpow__(self, other):
        """Create the Z3 expression `other**self` (** is the power operator).

        >>> x = Real('x')
        >>> 2**x
        2**x
        >>> (2**x).sort()
        Real
        """
        a, b = _coerce_exprs(self, other)
        return ArithRef(a.ctx.solver.mkTerm(kinds.Pow, b.ast, a.ast), self.ctx)

    def __div__(self, other):
        """Create the Z3 expression `other/self`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x/y
        x/y
        >>> (x/y).sort()
        Int
        >>> (x/y).sexpr()
        '(div x y)'
        >>> x = Real('x')
        >>> y = Real('y')
        >>> x/y
        x/y
        >>> (x/y).sort()
        Real
        >>> (x/y).sexpr()
        '(/ x y)'
        """
        a, b = _coerce_exprs(self, other)
        if a.sort() == IntSort(self.ctx):
            k = kinds.IntsDivision
        else:
            k = kinds.Division
        return ArithRef(a.ctx.solver.mkTerm(k, a.ast, b.ast), self.ctx)

    def __truediv__(self, other):
        """Create the Z3 expression `other/self`."""
        return self.__div__(other)

    def __rdiv__(self, other):
        """Create the Z3 expression `other/self`.

        >>> x = Int('x')
        >>> 10/x
        10/x
        >>> (10/x).sexpr()
        '(div 10 x)'
        >>> x = Real('x')
        >>> 10/x
        10/x
        >>> (10/x).sexpr()
        '(/ 10.0 x)'
        """
        a, b = _coerce_exprs(self, other)
        if a.sort() == IntSort(self.ctx):
            k = kinds.IntsDivision
        else:
            k = kinds.Division
        return ArithRef(a.ctx.solver.mkTerm(k, b.ast, a.ast), self.ctx)

    def __rtruediv__(self, other):
        """Create the Z3 expression `other/self`."""
        return self.__rdiv__(other)

    def __mod__(self, other):
        """Create the Z3 expression `other%self`.

        >>> x = Int('x')
        >>> y = Int('y')
        >>> x % y
        x%y
        """
        a, b = _coerce_exprs(self, other)
        if debugging():
            _assert(a.is_int(), "Z3 integer expression expected")
        return ArithRef(a.ctx.solver.mkTerm(kinds.IntsModulus, a.ast, b.ast), self.ctx)

    def __rmod__(self, other):
        """Create the Z3 expression `other%self`.

        >>> x = Int('x')
        >>> 10 % x
        10%x
        """
        a, b = _coerce_exprs(self, other)
        if debugging():
            _assert(a.is_int(), "Z3 integer expression expected")
        return ArithRef(a.ctx.solver.mkTerm(kinds.IntsModulus, b.ast, a.ast), self.ctx)

    def __neg__(self):
        """Return an expression representing `-self`.

        >>> x = Int('x')
        >>> -x
        -x
        """
        return ArithRef(self.ctx.solver.mkTerm(kinds.Uminus, self.ast), self.ctx)

    def __pos__(self):
        """Return `self`.

        >>> x = Int('x')
        >>> +x
        x
        """
        return self

    def __le__(self, other):
        """Create the Z3 expression `other <= self`.

        >>> x, y = Ints('x y')
        >>> x <= y
        x <= y
        >>> y = Real('y')
        >>> x <= y
        ToReal(x) <= y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(a.ctx.solver.mkTerm(kinds.Leq, a.ast, b.ast), self.ctx)

    def __lt__(self, other):
        """Create the Z3 expression `other < self`.

        >>> x, y = Ints('x y')
        >>> x < y
        x < y
        >>> y = Real('y')
        >>> x < y
        ToReal(x) < y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(a.ctx.solver.mkTerm(kinds.Lt, a.ast, b.ast), self.ctx)

    def __gt__(self, other):
        """Create the Z3 expression `other > self`.

        >>> x, y = Ints('x y')
        >>> x > y
        x > y
        >>> y = Real('y')
        >>> x > y
        ToReal(x) > y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(a.ctx.solver.mkTerm(kinds.Gt, a.ast, b.ast), self.ctx)

    def __ge__(self, other):
        """Create the Z3 expression `other >= self`.

        >>> x, y = Ints('x y')
        >>> x >= y
        x >= y
        >>> y = Real('y')
        >>> x >= y
        ToReal(x) >= y
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(a.ctx.solver.mkTerm(kinds.Geq, a.ast, b.ast), self.ctx)


def is_arith(a):
    """Return `True` if `a` is an arithmetical expression.

    >>> x = Int('x')
    >>> is_arith(x)
    True
    >>> is_arith(x + 1)
    True
    >>> is_arith(1)
    False
    >>> is_arith(IntVal(1))
    True
    >>> y = Real('y')
    >>> is_arith(y)
    True
    >>> is_arith(y + 1)
    True
    """
    return isinstance(a, ArithRef)


def is_int(a):
    """Return `True` if `a` is an integer expression.

    >>> x = Int('x')
    >>> is_int(x + 1)
    True
    >>> is_int(1)
    False
    >>> is_int(IntVal(1))
    True
    >>> y = Real('y')
    >>> is_int(y)
    False
    >>> is_int(y + 1)
    False
    """
    return is_arith(a) and a.is_int()


def is_real(a):
    """Return `True` if `a` is a real expression.

    >>> x = Int('x')
    >>> is_real(x + 1)
    False
    >>> y = Real('y')
    >>> is_real(y)
    True
    >>> is_real(y + 1)
    True
    >>> is_real(1)
    False
    >>> is_real(RealVal(1))
    True
    """
    return is_arith(a) and a.is_real()


def _is_numeral(ctx, term):
    return term.getKind() in [kinds.ConstRational, kinds.ConstBV, kinds.ConstBoolean]


def is_int_value(a):
    """Return `True` if `a` is an integer value of sort Int.

    >>> is_int_value(IntVal(1))
    True
    >>> is_int_value(1)
    False
    >>> is_int_value(Int('x'))
    False
    >>> n = Int('x') + 1
    >>> n
    x + 1
    >>> n.arg(1)
    1
    >>> is_int_value(n.arg(1))
    True
    >>> is_int_value(RealVal("1/3"))
    False
    >>> is_int_value(RealVal(1))
    False
    """
    return is_arith(a) and a.is_int() and _is_numeral(a.ctx, a.as_ast())


def is_rational_value(a):
    """Return `True` if `a` is rational value of sort Real.

    >>> is_rational_value(RealVal(1))
    True
    >>> is_rational_value(RealVal("3/5"))
    True
    >>> is_rational_value(IntVal(1))
    False
    >>> is_rational_value(1)
    False
    >>> n = Real('x') + 1
    >>> n.arg(1)
    1
    >>> is_rational_value(n.arg(1))
    True
    >>> is_rational_value(Real('x'))
    False
    """
    return is_arith(a) and a.is_real() and _is_numeral(a.ctx, a.as_ast())


def is_bool_value(a):
    """Return `True` if `a` is an integer value of sort Int.

    >>> is_bool_value(IntVal(1))
    False
    >>> is_bool_value(Bool('x'))
    False
    >>> is_bool_value(BoolVal(False))
    True
    """
    return is_bool(a) and _is_numeral(a.ctx, a.as_ast())


def is_add(a):
    """Return `True` if `a` is an expression of the form b + c.

    >>> x, y = Ints('x y')
    >>> is_add(x + y)
    True
    >>> is_add(x - y)
    False
    """
    return is_app_of(a, kinds.Plus)


def is_mul(a):
    """Return `True` if `a` is an expression of the form b * c.

    >>> x, y = Ints('x y')
    >>> is_mul(x * y)
    True
    >>> is_mul(x - y)
    False
    """
    return is_app_of(a, kinds.Mult)


def is_sub(a):
    """Return `True` if `a` is an expression of the form b - c.

    >>> x, y = Ints('x y')
    >>> is_sub(x - y)
    True
    >>> is_sub(x + y)
    False
    """
    return is_app_of(a, kinds.Minus)


def is_div(a):
    """Return `True` if `a` is an expression of the form b / c.

    >>> x, y = Reals('x y')
    >>> is_div(x / y)
    True
    >>> is_div(x + y)
    False
    >>> x, y = Ints('x y')
    >>> is_div(x / y)
    False
    >>> is_idiv(x / y)
    True
    """
    return is_app_of(a, kinds.Division)


def is_idiv(a):
    """Return `True` if `a` is an expression of the form b div c.

    >>> x, y = Ints('x y')
    >>> is_idiv(x / y)
    True
    >>> is_idiv(x + y)
    False
    """
    return is_app_of(a, kinds.IntsDivision)


def is_mod(a):
    """Return `True` if `a` is an expression of the form b % c.

    >>> x, y = Ints('x y')
    >>> is_mod(x % y)
    True
    >>> is_mod(x + y)
    False
    """
    return is_app_of(a, kinds.IntsModulus)


def is_le(a):
    """Return `True` if `a` is an expression of the form b <= c.

    >>> x, y = Ints('x y')
    >>> is_le(x <= y)
    True
    >>> is_le(x < y)
    False
    """
    return is_app_of(a, kinds.Leq)


def is_lt(a):
    """Return `True` if `a` is an expression of the form b < c.

    >>> x, y = Ints('x y')
    >>> is_lt(x < y)
    True
    >>> is_lt(x == y)
    False
    """
    return is_app_of(a, kinds.Lt)


def is_ge(a):
    """Return `True` if `a` is an expression of the form b >= c.

    >>> x, y = Ints('x y')
    >>> is_ge(x >= y)
    True
    >>> is_ge(x == y)
    False
    """
    return is_app_of(a, kinds.Geq)


def is_gt(a):
    """Return `True` if `a` is an expression of the form b > c.

    >>> x, y = Ints('x y')
    >>> is_gt(x > y)
    True
    >>> is_gt(x == y)
    False
    """
    return is_app_of(a, kinds.Gt)


def is_is_int(a):
    """Return `True` if `a` is an expression of the form IsInt(b).

    >>> x = Real('x')
    >>> is_is_int(IsInt(x))
    True
    >>> is_is_int(x)
    False
    """
    return is_app_of(a, kinds.IsInteger)


def is_to_real(a):
    """Return `True` if `a` is an expression of the form ToReal(b).

    >>> x = Int('x')
    >>> n = ToReal(x)
    >>> n
    ToReal(x)
    >>> is_to_real(n)
    True
    >>> is_to_real(x)
    False
    """
    return is_app_of(a, kinds.ToReal)


def is_to_int(a):
    """Return `True` if `a` is an expression of the form ToInt(b).

    >>> x = Real('x')
    >>> n = ToInt(x)
    >>> n
    ToInt(x)
    >>> is_to_int(n)
    True
    >>> is_to_int(x)
    False
    """
    return is_app_of(a, kinds.ToInteger)


class IntNumRef(ArithRef):
    """Integer values."""

    def as_long(self):
        """Return a Z3 integer numeral as a Python long (bignum) numeral.

        >>> v = IntVal(1)
        >>> v + 1
        1 + 1
        >>> v.as_long() + 1
        2
        """
        if debugging():
            _assert(self.is_int(), "Integer value expected")
        return int(self.as_string())

    def as_string(self):
        """Return a Z3 integer numeral as a Python string.
        >>> v = IntVal(100)
        >>> v.as_string()
        '100'
        """
        return str(self.ast.toPythonObj())

    def as_binary_string(self):
        """Return a Z3 integer numeral as a Python binary string.
        >>> v = IntVal(10)
        >>> v.as_binary_string()
        '1010'
        """
        return "{:b}".format(int(self.as_string()))


class RatNumRef(ArithRef):
    """Rational values."""

    def numerator(self):
        """Return the numerator of a Z3 rational numeral.

        >>> is_rational_value(RealVal("3/5"))
        True
        >>> n = RealVal("3/5")
        >>> n.numerator()
        3
        >>> is_rational_value(Q(3,5))
        True
        >>> Q(3,5).numerator()
        3
        """
        return self.as_fraction().numerator

    def denominator(self):
        """Return the denominator of a Z3 rational numeral.

        >>> is_rational_value(Q(3,5))
        True
        >>> n = Q(3,5)
        >>> n.denominator()
        5
        """
        return self.as_fraction().denominator

    def numerator_as_long(self):
        """Return the numerator as a Python long.

        >>> v = RealVal(10000000000)
        >>> v
        10000000000
        >>> v + 1
        10000000000 + 1
        >>> v.numerator_as_long() + 1 == 10000000001
        True
        """
        return self.as_fraction().numerator

    def denominator_as_long(self):
        """Return the denominator as a Python long.

        >>> v = RealVal("1/3")
        >>> v
        1/3
        >>> v.denominator_as_long()
        3
        """
        return self.as_fraction().denominator

    def is_int(self):
        return False

    def is_real(self):
        return True

    def is_int_value(self):
        return self.denominator().is_int() and self.denominator_as_long() == 1

    def as_long(self):
        _assert(self.is_int_value(), "Expected integer fraction")
        return self.numerator_as_long()

    def as_decimal(self, prec):
        """Return a Z3 rational value as a string in decimal notation using at most `prec` decimal places.

        >>> v = RealVal("1/5")
        >>> v.as_decimal(3)
        '0.2'
        >>> v = RealVal("1/3")
        >>> v.as_decimal(3)
        '0.333'
        """
        f = self.as_fraction()
        decimal.getcontext().prec = prec
        return str(Decimal(f.numerator) / Decimal(f.denominator))

    def as_string(self):
        """Return a Z3 rational numeral as a Python string.

        >>> v = Q(3,6)
        >>> v.as_string()
        '1/2'
        """
        r = self.as_fraction()
        if r.denominator == 1:
            return "{}".format(r.numerator)
        else:
            return "{}/{}".format(r.numerator, r.denominator)

    def as_fraction(self):
        """Return a Z3 rational as a Python Fraction object.

        >>> v = RealVal("1/5")
        >>> v.as_fraction()
        Fraction(1, 5)
        """
        return self.ast.toPythonObj()


def _py2expr(a, ctx=None):
    if isinstance(a, bool):
        return BoolVal(a, ctx)
    if _is_int(a):
        return IntVal(a, ctx)
    if isinstance(a, float):
        return RealVal(a, ctx)
    if is_expr(a):
        return a
    if debugging():
        _assert(False, "Python bool, int, long or float expected")


def IntSort(ctx=None):
    """Return the integer sort in the given context. If `ctx=None`, then the global context is used.

    >>> IntSort()
    Int
    >>> x = Const('x', IntSort())
    >>> is_int(x)
    True
    >>> x.sort() == IntSort()
    True
    >>> x.sort() == BoolSort()
    False
    """
    ctx = _get_ctx(ctx)
    return ArithSortRef(ctx.solver.getIntegerSort(), ctx)


def RealSort(ctx=None):
    """Return the real sort in the given context. If `ctx=None`, then the global context is used.

    >>> RealSort()
    Real
    >>> x = Const('x', RealSort())
    >>> is_real(x)
    True
    >>> is_int(x)
    False
    >>> x.sort() == RealSort()
    True
    """
    ctx = _get_ctx(ctx)
    return ArithSortRef(ctx.solver.getRealSort(), ctx)


def _to_int_str(val):
    if isinstance(val, float):
        return str(int(val))
    elif isinstance(val, bool):
        if val:
            return "1"
        else:
            return "0"
    elif _is_int(val):
        return str(val)
    elif isinstance(val, str):
        return val
    if debugging():
        _assert(False, "Python value cannot be used as a Z3 integer")


def IntVal(val, ctx=None):
    """Return a Z3 integer value. If `ctx=None`, then the global context is used.

    >>> IntVal(1)
    1
    >>> IntVal("100")
    100
    """
    ctx = _get_ctx(ctx)
    return IntNumRef(ctx.solver.mkInteger(_to_int_str(val)), ctx)


def RealVal(val, ctx=None):
    """Return a Z3 real value.

    `val` may be a Python int, long, float or string representing a number in decimal or rational notation.
    If `ctx=None`, then the global context is used.

    >>> RealVal(1)
    1
    >>> RealVal(1).sort()
    Real
    >>> RealVal("3/5")
    3/5
    >>> RealVal("1.5")
    3/2
    """
    ctx = _get_ctx(ctx)
    return RatNumRef(ctx.solver.mkReal(str(val)), ctx)


def RatVal(a, b, ctx=None):
    """Return a Z3 rational a/b.

    If `ctx=None`, then the global context is used.

    >>> RatVal(3,5)
    3/5
    >>> RatVal(3,5).sort()
    Real
    """
    if debugging():
        _assert(
            _is_int(a) or isinstance(a, str),
            "First argument cannot be converted into an integer",
        )
        _assert(
            _is_int(b) or isinstance(b, str),
            "Second argument cannot be converted into an integer",
        )
    return simplify(RealVal(a, ctx) / RealVal(b, ctx))


def Q(a, b, ctx=None):
    """Return a Z3 rational a/b.

    If `ctx=None`, then the global context is used.

    >>> Q(3,5)
    3/5
    >>> Q(3,5).sort()
    Real
    """
    return simplify(RatVal(a, b))


def Int(name, ctx=None):
    """Return an integer constant named `name`. If `ctx=None`, then the global context is used.

    >>> x = Int('x')
    >>> is_int(x)
    True
    >>> is_int(x + 1)
    True
    """
    ctx = _get_ctx(ctx)
    e = ctx.get_var(name, IntSort(ctx))
    return ArithRef(e, ctx)


def Ints(names, ctx=None):
    """Return a tuple of Integer constants.

    >>> x, y, z = Ints('x y z')
    >>> Sum(x, y, z)
    x + y + z
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [Int(name, ctx) for name in names]


def IntVector(prefix, sz, ctx=None):
    """Return a list of integer constants of size `sz`.

    >>> X = IntVector('x', 3)
    >>> X
    [x__0, x__1, x__2]
    >>> Sum(X)
    x__0 + x__1 + x__2
    """
    ctx = _get_ctx(ctx)
    return [Int("%s__%s" % (prefix, i), ctx) for i in range(sz)]


def FreshInt(prefix="x", ctx=None):
    """Return a fresh integer constant in the given context using the given prefix.

    >>> x = FreshInt()
    >>> y = FreshInt()
    >>> eq(x, y)
    False
    >>> x.sort()
    Int
    """
    ctx = _get_ctx(ctx)
    sort = IntSort(ctx)
    name = ctx.next_fresh(sort, prefix)
    return Int(name, ctx)


def Real(name, ctx=None):
    """Return a real constant named `name`. If `ctx=None`, then the global context is used.

    >>> x = Real('x')
    >>> is_real(x)
    True
    >>> is_real(x + 1)
    True
    """
    ctx = _get_ctx(ctx)
    e = ctx.get_var(name, RealSort(ctx))
    return ArithRef(e, ctx)


def Reals(names, ctx=None):
    """Return a tuple of real constants.

    >>> x, y, z = Reals('x y z')
    >>> Sum(x, y, z)
    x + y + z
    >>> Sum(x, y, z).sort()
    Real
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [Real(name, ctx) for name in names]


def RealVector(prefix, sz, ctx=None):
    """Return a list of real constants of size `sz`.

    >>> X = RealVector('x', 3)
    >>> X
    [x__0, x__1, x__2]
    >>> Sum(X)
    x__0 + x__1 + x__2
    >>> Sum(X).sort()
    Real
    """
    ctx = _get_ctx(ctx)
    return [Real("%s__%s" % (prefix, i), ctx) for i in range(sz)]


def FreshReal(prefix="b", ctx=None):
    """Return a fresh real constant in the given context using the given prefix.

    >>> x = FreshReal()
    >>> y = FreshReal()
    >>> eq(x, y)
    False
    >>> x.sort()
    Real
    """
    ctx = _get_ctx(ctx)
    sort = RealSort(ctx)
    name = ctx.next_fresh(sort, prefix)
    return Real(name, ctx)


def ToReal(a):
    """Return the Z3 expression ToReal(a).

    >>> x = Int('x')
    >>> x.sort()
    Int
    >>> n = ToReal(x)
    >>> n
    ToReal(x)
    >>> n.sort()
    Real
    """
    if debugging():
        _assert(a.is_int(), "Z3 integer expression expected.")
    ctx = a.ctx
    return ArithRef(ctx.solver.mkTerm(kinds.ToReal, a.ast), ctx)


def ToInt(a):
    """Return the Z3 expression ToInt(a).

    >>> x = Real('x')
    >>> x.sort()
    Real
    >>> n = ToInt(x)
    >>> n
    ToInt(x)
    >>> n.sort()
    Int
    """
    if debugging():
        _assert(a.is_real(), "Z3 real expression expected.")
    ctx = a.ctx
    return ArithRef(ctx.solver.mkTerm(kinds.ToInteger, a.ast), ctx)


def IsInt(a):
    """Return the Z3 predicate IsInt(a).

    >>> x = Real('x')
    >>> IsInt(x + "1/2")
    IsInt(x + 1/2)
    >>> solve(IsInt(x + "1/2"), x > 0, x < 1)
    [x = 1/2]
    >>> solve(IsInt(x + "1/2"), x > 0, x < 1, x != "1/2")
    no solution
    """
    if debugging():
        _assert(a.is_real(), "Z3 real expression expected.")
    ctx = a.ctx
    return BoolRef(ctx.solver.mkTerm(kinds.IsInteger, a.ast), ctx)


def Sqrt(a, ctx=None):
    """Return a Z3 expression which represents the square root of a.

    >>> x = Real('x')
    >>> Sqrt(x)
    x**(1/2)
    """
    if not is_expr(a):
        ctx = _get_ctx(ctx)
        a = RealVal(a, ctx)
    return a ** "1/2"


def Cbrt(a, ctx=None):
    """Return a Z3 expression which represents the cubic root of a.

    >>> x = Real('x')
    >>> Cbrt(x)
    x**(1/3)
    """
    if not is_expr(a):
        ctx = _get_ctx(ctx)
        a = RealVal(a, ctx)
    return a ** "1/3"


#########################################
#
# Bit-Vectors
#
#########################################


class BitVecSortRef(SortRef):
    """Bit-vector sort."""

    def size(self):
        """Return the size (number of bits) of the bit-vector sort `self`.

        >>> b = BitVecSort(32)
        >>> b.size()
        32
        """
        return self.ast.getBVSize()

    def subsort(self, other):
        return is_bv_sort(other) and self.size() < other.size()

    def cast(self, val):
        """Try to cast `val` as a Bit-Vector.

        >>> b = BitVecSort(32)
        >>> b.cast(10)
        10
        >>> b.cast(10).sexpr()
        '#b00000000000000000000000000001010'
        """
        if is_expr(val):
            if debugging():
                _assert(self.ctx == val.ctx, "Context mismatch")
            # Idea: use sign_extend if sort of val is a bitvector of smaller size
            return val
        else:
            return BitVecVal(val, self)


def is_bv_sort(s):
    """Return True if `s` is a Z3 bit-vector sort.

    >>> is_bv_sort(BitVecSort(32))
    True
    >>> is_bv_sort(IntSort())
    False
    """
    return isinstance(s, BitVecSortRef)


class BitVecRef(ExprRef):
    """Bit-vector expressions."""

    def sort(self):
        """Return the sort of the bit-vector expression `self`.

        >>> x = BitVec('x', 32)
        >>> x.sort()
        BitVec(32)
        >>> x.sort() == BitVecSort(32)
        True
        """
        return _sort(self.ctx, self.ast)

    def size(self):
        """Return the number of bits of the bit-vector expression `self`.

        >>> x = BitVec('x', 32)
        >>> (x + 1).size()
        32
        >>> Concat(x, x).size()
        64
        """
        return self.sort().size()

    def __add__(self, other):
        """Create the Z3 expression `self + other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x + y
        x + y
        >>> (x + y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVPlus, a.ast, b.ast), self.ctx)

    def __radd__(self, other):
        """Create the Z3 expression `other + self`.

        >>> x = BitVec('x', 32)
        >>> 10 + x
        10 + x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVPlus, b.ast, a.ast), self.ctx)

    def __mul__(self, other):
        """Create the Z3 expression `self * other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x * y
        x*y
        >>> (x * y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVMult, a.ast, b.ast), self.ctx)

    def __rmul__(self, other):
        """Create the Z3 expression `other * self`.

        >>> x = BitVec('x', 32)
        >>> 10 * x
        10*x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVMult, b.ast, a.ast), self.ctx)

    def __sub__(self, other):
        """Create the Z3 expression `self - other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x - y
        x - y
        >>> (x - y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSub, a.ast, b.ast), self.ctx)

    def __rsub__(self, other):
        """Create the Z3 expression `other - self`.

        >>> x = BitVec('x', 32)
        >>> 10 - x
        10 - x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSub, b.ast, a.ast), self.ctx)

    def __or__(self, other):
        """Create the Z3 expression bitwise-or `self | other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x | y
        x | y
        >>> (x | y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVOr, a.ast, b.ast), self.ctx)

    def __ror__(self, other):
        """Create the Z3 expression bitwise-or `other | self`.

        >>> x = BitVec('x', 32)
        >>> 10 | x
        10 | x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVOr, b.ast, a.ast), self.ctx)

    def __and__(self, other):
        """Create the Z3 expression bitwise-and `self & other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x & y
        x & y
        >>> (x & y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVAnd, a.ast, b.ast), self.ctx)

    def __rand__(self, other):
        """Create the Z3 expression bitwise-or `other & self`.

        >>> x = BitVec('x', 32)
        >>> 10 & x
        10 & x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVAnd, b.ast, a.ast), self.ctx)

    def __xor__(self, other):
        """Create the Z3 expression bitwise-xor `self ^ other`.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x ^ y
        x ^ y
        >>> (x ^ y).sort()
        BitVec(32)
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVXor, a.ast, b.ast), self.ctx)

    def __rxor__(self, other):
        """Create the Z3 expression bitwise-xor `other ^ self`.

        >>> x = BitVec('x', 32)
        >>> 10 ^ x
        10 ^ x
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVXor, b.ast, a.ast), self.ctx)

    def __pos__(self):
        """Return `self`.

        >>> x = BitVec('x', 32)
        >>> +x
        x
        """
        return self

    def __neg__(self):
        """Return an expression representing `-self`.

        >>> x = BitVec('x', 32)
        >>> -x
        -x
        >>> solve([-(-x) != x])
        no solution
        """
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVNeg, self.ast), self.ctx)

    def __invert__(self):
        """Create the Z3 expression bitwise-not `~self`.

        >>> x = BitVec('x', 32)
        >>> ~x
        ~x
        >>> solve([~(~x) != x])
        no solution
        """
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVNot, self.ast), self.ctx)

    def __div__(self, other):
        """Create the Z3 expression (signed) division `self / other`.

        Use the function UDiv() for unsigned division.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x / y
        x/y
        >>> (x / y).sort()
        BitVec(32)
        >>> (x / y).sexpr()
        '(bvsdiv x y)'
        >>> UDiv(x, y).sexpr()
        '(bvudiv x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSdiv, a.ast, b.ast), self.ctx)

    def __truediv__(self, other):
        """Create the Z3 expression (signed) division `self / other`."""
        return self.__div__(other)

    def __rdiv__(self, other):
        """Create the Z3 expression (signed) division `other / self`.

        Use the function UDiv() for unsigned division.

        >>> x = BitVec('x', 32)
        >>> 10 / x
        10/x
        >>> (10 / x).sexpr()
        '(bvsdiv #b00000000000000000000000000001010 x)'
        >>> UDiv(10, x).sexpr()
        '(bvudiv #b00000000000000000000000000001010 x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSdiv, b.ast, a.ast), self.ctx)

    def __rtruediv__(self, other):
        """Create the Z3 expression (signed) division `other / self`."""
        return self.__rdiv__(other)

    def __mod__(self, other):
        """Create the Z3 expression (signed) mod `self % other`.

        Use the function URem() for unsigned remainder, and SRem() for signed remainder.

        >>> x = BitVec('x', 32)
        >>> y = BitVec('y', 32)
        >>> x % y
        x%y
        >>> (x % y).sort()
        BitVec(32)
        >>> (x % y).sexpr()
        '(bvsmod x y)'
        >>> URem(x, y).sexpr()
        '(bvurem x y)'
        >>> SRem(x, y).sexpr()
        '(bvsrem x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSmod, a.ast, b.ast), self.ctx)

    def __rmod__(self, other):
        """Create the Z3 expression (signed) mod `other % self`.

        Use the function URem() for unsigned remainder, and SRem() for signed remainder.

        >>> x = BitVec('x', 32)
        >>> 10 % x
        10%x
        >>> (10 % x).sexpr()
        '(bvsmod #b00000000000000000000000000001010 x)'
        >>> URem(10, x).sexpr()
        '(bvurem #b00000000000000000000000000001010 x)'
        >>> SRem(10, x).sexpr()
        '(bvsrem #b00000000000000000000000000001010 x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVSmod, b.ast, a.ast), self.ctx)

    def __le__(self, other):
        """Create the Z3 expression (signed) `other <= self`.

        Use the function ULE() for unsigned less than or equal to.

        >>> x, y = BitVecs('x y', 32)
        >>> x <= y
        x <= y
        >>> (x <= y).sexpr()
        '(bvsle x y)'
        >>> ULE(x, y).sexpr()
        '(bvule x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(self.ctx.solver.mkTerm(kinds.BVSle, a.ast, b.ast), self.ctx)

    def __lt__(self, other):
        """Create the Z3 expression (signed) `other < self`.

        Use the function ULT() for unsigned less than.

        >>> x, y = BitVecs('x y', 32)
        >>> x < y
        x < y
        >>> (x < y).sexpr()
        '(bvslt x y)'
        >>> ULT(x, y).sexpr()
        '(bvult x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(self.ctx.solver.mkTerm(kinds.BVSlt, a.ast, b.ast), self.ctx)

    def __gt__(self, other):
        """Create the Z3 expression (signed) `other > self`.

        Use the function UGT() for unsigned greater than.

        >>> x, y = BitVecs('x y', 32)
        >>> x > y
        x > y
        >>> (x > y).sexpr()
        '(bvsgt x y)'
        >>> UGT(x, y).sexpr()
        '(bvugt x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(self.ctx.solver.mkTerm(kinds.BVSgt, a.ast, b.ast), self.ctx)

    def __ge__(self, other):
        """Create the Z3 expression (signed) `other >= self`.

        Use the function UGE() for unsigned greater than or equal to.

        >>> x, y = BitVecs('x y', 32)
        >>> x >= y
        x >= y
        >>> (x >= y).sexpr()
        '(bvsge x y)'
        >>> UGE(x, y).sexpr()
        '(bvuge x y)'
        """
        a, b = _coerce_exprs(self, other)
        return BoolRef(self.ctx.solver.mkTerm(kinds.BVSge, a.ast, b.ast), self.ctx)

    def __rshift__(self, other):
        """Create the Z3 expression (arithmetical) right shift `self >> other`

        Use the function LShR() for the right logical shift

        >>> x, y = BitVecs('x y', 32)
        >>> x >> y
        x >> y
        >>> (x >> y).sexpr()
        '(bvashr x y)'
        >>> LShR(x, y).sexpr()
        '(bvlshr x y)'
        >>> BitVecVal(4, 3)
        4
        >>> BitVecVal(4, 3).as_signed_long()
        -4
        >>> evaluate(BitVecVal(4, 3) >> 1).as_signed_long()
        -2
        >>> evaluate(BitVecVal(4, 3) >> 1)
        6
        >>> evaluate(LShR(BitVecVal(4, 3), 1))
        2
        >>> evaluate(BitVecVal(2, 3) >> 1)
        1
        >>> evaluate(LShR(BitVecVal(2, 3), 1))
        1
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVAshr, a.ast, b.ast), self.ctx)

    def __lshift__(self, other):
        """Create the Z3 expression left shift `self << other`

        >>> x, y = BitVecs('x y', 32)
        >>> x << y
        x << y
        >>> (x << y).sexpr()
        '(bvshl x y)'
        >>> evaluate(BitVecVal(2, 3) << 1)
        4
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVShl, a.ast, b.ast), self.ctx)

    def __rrshift__(self, other):
        """Create the Z3 expression (arithmetical) right shift `other` >> `self`.

        Use the function LShR() for the right logical shift

        >>> x = BitVec('x', 32)
        >>> 10 >> x
        10 >> x
        >>> (10 >> x).sexpr()
        '(bvashr #b00000000000000000000000000001010 x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVAshr, b.ast, a.ast), self.ctx)

    def __rlshift__(self, other):
        """Create the Z3 expression left shift `other << self`.

        Use the function LShR() for the right logical shift

        >>> x = BitVec('x', 32)
        >>> 10 << x
        10 << x
        >>> (10 << x).sexpr()
        '(bvshl #b00000000000000000000000000001010 x)'
        """
        a, b = _coerce_exprs(self, other)
        return BitVecRef(self.ctx.solver.mkTerm(kinds.BVShl, b.ast, a.ast), self.ctx)


class BitVecNumRef(BitVecRef):
    """Bit-vector values."""

    def as_long(self):
        """Return a Z3 bit-vector numeral as a Python long (bignum) numeral.

        >>> v = BitVecVal(0xbadc0de, 32)
        >>> v
        195936478
        >>> print("0x%.8x" % v.as_long())
        0x0badc0de
        """
        return int(self.as_string())

    def as_signed_long(self):
        """Return a Z3 bit-vector numeral as a Python long (bignum) numeral. The most significant bit is assumed to be the sign.

        >>> BitVecVal(4, 3).as_signed_long()
        -4
        >>> BitVecVal(7, 3).as_signed_long()
        -1
        >>> BitVecVal(3, 3).as_signed_long()
        3
        >>> BitVecVal(2**32 - 1, 32).as_signed_long()
        -1
        >>> BitVecVal(2**64 - 1, 64).as_signed_long()
        -1
        """
        sz = self.size()
        val = self.as_long()
        if val >= 2 ** (sz - 1):
            val = val - 2 ** sz
        if val < -(2 ** (sz - 1)):
            val = val + 2 ** sz
        return int(val)

    def as_string(self):
        return str(int(self.as_binary_string(), 2))

    def as_binary_string(self):
        return str(self.ast)[2:]


def is_bv(a):
    """Return `True` if `a` is a Z3 bit-vector expression.

    >>> b = BitVec('b', 32)
    >>> is_bv(b)
    True
    >>> is_bv(b + 10)
    True
    >>> is_bv(Int('x'))
    False
    """
    return isinstance(a, BitVecRef)


def is_bv_value(a):
    """Return `True` if `a` is a Z3 bit-vector numeral value.

    >>> b = BitVec('b', 32)
    >>> is_bv_value(b)
    False
    >>> b = BitVecVal(10, 32)
    >>> b
    10
    >>> is_bv_value(b)
    True
    """
    return is_bv(a) and _is_numeral(a.ctx, a.as_ast())


def BV2Int(a, is_signed=False):
    """Return the Z3 expression BV2Int(a).

    >>> b = BitVec('b', 3)
    >>> BV2Int(b).sort()
    Int
    >>> x = Int('x')
    >>> x > BV2Int(b)
    x > BV2Int(b)
    >>> x > BV2Int(b, is_signed=False)
    x > BV2Int(b)
    >>> x > BV2Int(b, is_signed=True)
    x > If(b < 0, BV2Int(b) - 8, BV2Int(b))
    >>> solve(x > BV2Int(b), b == 1, x < 3)
    [b = 1, x = 2]
    """
    if debugging():
        _assert(is_bv(a), "First argument must be a Z3 bit-vector expression")
    ctx = a.ctx
    if is_signed:
        w = a.sort().size()
        nat = BV2Int(a)
        return If(a < 0, nat - (2 ** w), nat)
    else:
        # investigate problem with bv2int
        return ArithRef(ctx.solver.mkTerm(kinds.BVToNat, a.ast), ctx)


def Int2BV(a, num_bits):
    """Return the z3 expression Int2BV(a, num_bits).
    It is a bit-vector of width num_bits and represents the
    modulo of a by 2^num_bits
    """
    ctx = a.ctx
    return BitVecRef(ctx.solver.mkTerm(ctx.mkOp(kinds.IntToBV, num_bits), a.ast), ctx)


def BitVecSort(sz, ctx=None):
    """Return a Z3 bit-vector sort of the given size. If `ctx=None`, then the global context is used.

    >>> Byte = BitVecSort(8)
    >>> Word = BitVecSort(16)
    >>> Byte
    BitVec(8)
    >>> x = Const('x', Byte)
    >>> eq(x, BitVec('x', 8))
    True
    """
    ctx = _get_ctx(ctx)
    return BitVecSortRef(ctx.solver.mkBitVectorSort(sz), ctx)


def BitVecVal(val, bv, ctx=None):
    """Return a bit-vector value with the given number of bits. If `ctx=None`, then the global context is used.

    >>> v = BitVecVal(10, 32)
    >>> v
    10
    >>> print("0x%.8x" % v.as_long())
    0x0000000a
    """
    if is_bv_sort(bv):
        ctx = bv.ctx
        size = bv.size()
    else:
        size = bv
        ctx = _get_ctx(ctx)
    string = "{{:0{}b}}".format(size).format(val)
    return BitVecNumRef(ctx.solver.mkBitVector(string), ctx)


def BitVec(name, bv, ctx=None):
    """Return a bit-vector constant named `name`. `bv` may be the number of bits of a bit-vector sort.
    If `ctx=None`, then the global context is used.

    >>> x  = BitVec('x', 16)
    >>> is_bv(x)
    True
    >>> x.size()
    16
    >>> x.sort()
    BitVec(16)
    >>> word = BitVecSort(16)
    >>> x2 = BitVec('x', word)
    >>> eq(x, x2)
    True
    """
    if isinstance(bv, BitVecSortRef):
        ctx = bv.ctx
    else:
        ctx = _get_ctx(ctx)
        bv = BitVecSort(bv, ctx)
    e = ctx.get_var(name, bv)
    return BitVecRef(e, ctx)


def BitVecs(names, bv, ctx=None):
    """Return a tuple of bit-vector constants of size bv.

    >>> x, y, z = BitVecs('x y z', 16)
    >>> x.size()
    16
    >>> x.sort()
    BitVec(16)
    >>> Sum(x, y, z)
    0 + x + y + z
    >>> Product(x, y, z)
    x*y*z
    """
    ctx = _get_ctx(ctx)
    if isinstance(names, str):
        names = names.split(" ")
    return [BitVec(name, bv, ctx) for name in names]


def Concat(*args):
    """Create a Z3 bit-vector concatenation expression.

    >>> v = BitVecVal(1, 4)
    >>> Concat(v, v+1, v)
    Concat(1, 1 + 1, 1)
    >>> evaluate(Concat(v, v+1, v))
    289
    >>> print("%.3x" % simplify(Concat(v, v+1, v)).as_long())
    121
    """
    args = _get_args(args)
    sz = len(args)
    if debugging():
        _assert(sz >= 2, "At least two arguments expected.")

    ctx = None
    for a in args:
        if is_expr(a):
            ctx = a.ctx
            break
    if debugging():
        _assert(
            all([is_bv(a) for a in args]),
            "All arguments must be Z3 bit-vector expressions.",
        )
    return BitVecRef(ctx.solver.mkTerm(kinds.BVConcat, *[a.ast for a in args]))


def Extract(high, low, a):
    """Create a Z3 bit-vector extraction expression, or create a string extraction expression.

    >>> x = BitVec('x', 8)
    >>> Extract(6, 2, x)
    Extract(6, 2, x)
    >>> Extract(6, 2, x).sort()
    BitVec(5)
    """
    if isinstance(high, str):
        high = StringVal(high)
    if debugging():
        _assert(
            low <= high,
            "First argument must be greater than or equal to second argument",
        )
        _assert(
            _is_int(high) and high >= 0 and _is_int(low) and low >= 0,
            "First and second arguments must be non negative integers",
        )
        _assert(is_bv(a), "Third argument must be a Z3 bit-vector expression")
    return BitVecRef(
        a.ctx.solver.mkTerm(a.ctx.solver.mkOp(kinds.BVExtract, high, low), a.ast), a.ctx
    )


def _check_bv_args(a, b):
    if debugging():
        _assert(
            is_bv(a) or is_bv(b),
            "First or second argument must be a Z3 bit-vector expression",
        )


def ULE(a, b):
    """Create the Z3 expression (unsigned) `other <= self`.

    Use the operator <= for signed less than or equal to.

    >>> x, y = BitVecs('x y', 32)
    >>> ULE(x, y)
    ULE(x, y)
    >>> (x <= y).sexpr()
    '(bvsle x y)'
    >>> ULE(x, y).sexpr()
    '(bvule x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(kinds.BVUle, a.ast, b.ast), a.ctx)


def ULT(a, b):
    """Create the Z3 expression (unsigned) `other < self`.

    Use the operator < for signed less than.

    >>> x, y = BitVecs('x y', 32)
    >>> ULT(x, y)
    ULT(x, y)
    >>> (x < y).sexpr()
    '(bvslt x y)'
    >>> ULT(x, y).sexpr()
    '(bvult x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(kinds.BVUlt, a.ast, b.ast), a.ctx)


def UGE(a, b):
    """Create the Z3 expression (unsigned) `other >= self`.

    Use the operator >= for signed greater than or equal to.

    >>> x, y = BitVecs('x y', 32)
    >>> UGE(x, y)
    UGE(x, y)
    >>> (x >= y).sexpr()
    '(bvsge x y)'
    >>> UGE(x, y).sexpr()
    '(bvuge x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(kinds.BVUge, a.ast, b.ast), a.ctx)


def UGT(a, b):
    """Create the Z3 expression (unsigned) `other > self`.

    Use the operator > for signed greater than.

    >>> x, y = BitVecs('x y', 32)
    >>> UGT(x, y)
    UGT(x, y)
    >>> (x > y).sexpr()
    '(bvsgt x y)'
    >>> UGT(x, y).sexpr()
    '(bvugt x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BoolRef(a.ctx.solver.mkTerm(kinds.BVUgt, a.ast, b.ast), a.ctx)


def UDiv(a, b):
    """Create the Z3 expression (unsigned) division `self / other`.

    Use the operator / for signed division.

    >>> x = BitVec('x', 32)
    >>> y = BitVec('y', 32)
    >>> UDiv(x, y)
    UDiv(x, y)
    >>> UDiv(x, y).sort()
    BitVec(32)
    >>> (x / y).sexpr()
    '(bvsdiv x y)'
    >>> UDiv(x, y).sexpr()
    '(bvudiv x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVUdiv, a.ast, b.ast), a.ctx)


def URem(a, b):
    """Create the Z3 expression (unsigned) remainder `self % other`.

    Use the operator % for signed modulus, and SRem() for signed remainder.

    >>> x = BitVec('x', 32)
    >>> y = BitVec('y', 32)
    >>> URem(x, y)
    URem(x, y)
    >>> URem(x, y).sort()
    BitVec(32)
    >>> (x % y).sexpr()
    '(bvsmod x y)'
    >>> URem(x, y).sexpr()
    '(bvurem x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVUrem, a.ast, b.ast), a.ctx)


def SRem(a, b):
    """Create the Z3 expression signed remainder.

    Use the operator % for signed modulus, and URem() for unsigned remainder.

    >>> x = BitVec('x', 32)
    >>> y = BitVec('y', 32)
    >>> SRem(x, y)
    SRem(x, y)
    >>> SRem(x, y).sort()
    BitVec(32)
    >>> (x % y).sexpr()
    '(bvsmod x y)'
    >>> SRem(x, y).sexpr()
    '(bvsrem x y)'
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVSrem, a.ast, b.ast), a.ctx)


def LShR(a, b):
    """Create the Z3 expression logical right shift.

    Use the operator >> for the arithmetical right shift.

    >>> x, y = BitVecs('x y', 32)
    >>> LShR(x, y)
    LShR(x, y)
    >>> (x >> y).sexpr()
    '(bvashr x y)'
    >>> LShR(x, y).sexpr()
    '(bvlshr x y)'
    >>> BitVecVal(4, 3)
    4
    >>> BitVecVal(4, 3).as_signed_long()
    -4
    >>> simplify(BitVecVal(4, 3) >> 1).as_signed_long()
    -2
    >>> simplify(BitVecVal(4, 3) >> 1)
    6
    >>> simplify(LShR(BitVecVal(4, 3), 1))
    2
    >>> simplify(BitVecVal(2, 3) >> 1)
    1
    >>> simplify(LShR(BitVecVal(2, 3), 1))
    1
    """
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVLshr, a.ast, b.ast), a.ctx)


def RotateLeft(a, b):
    """Return an expression representing `a` rotated to the left `b` times.

    >>> a, b = BitVecs('a b', 16)
    >>> RotateLeft(a, 10)
    RotateLeft(a, 10)
    >>> simplify(RotateLeft(a, 0))
    a
    >>> simplify(RotateLeft(a, 16))
    a
    """
    s = a.ctx.solver
    return BitVecRef(s.mkTerm(s.mkOp(kinds.BVRotateLeft, b), a.ast), a.ctx)


def RotateRight(a, b):
    """Return an expression representing `a` rotated to the right `b` times.

    >>> a, b = BitVecs('a b', 16)
    >>> RotateRight(a, 10)
    RotateRight(a, 10)
    >>> simplify(RotateRight(a, 0))
    a
    >>> simplify(RotateRight(a, 16))
    a
    """
    s = a.ctx.solver
    return BitVecRef(s.mkTerm(s.mkOp(kinds.BVRotateRight, b), a.ast), a.ctx)


def SignExt(n, a):
    """Return a bit-vector expression with `n` extra sign-bits.

    >>> x = BitVec('x', 16)
    >>> n = SignExt(8, x)
    >>> n.size()
    24
    >>> n
    SignExt(8, x)
    >>> n.sort()
    BitVec(24)
    >>> v0 = BitVecVal(2, 2)
    >>> v0
    2
    >>> v0.size()
    2
    >>> v  = simplify(SignExt(6, v0))
    >>> v
    254
    >>> v.size()
    8
    >>> print("%.x" % v.as_long())
    fe
    """
    if debugging():
        _assert(_is_int(n), "First argument must be an integer")
        _assert(is_bv(a), "Second argument must be a Z3 bit-vector expression")
    s = a.ctx.solver
    return BitVecRef(s.mkTerm(s.mkOp(kinds.BVSignExtend, n), a.ast), a.ctx)


def ZeroExt(n, a):
    """Return a bit-vector expression with `n` extra zero-bits.

    >>> x = BitVec('x', 16)
    >>> n = ZeroExt(8, x)
    >>> n.size()
    24
    >>> n
    ZeroExt(8, x)
    >>> n.sort()
    BitVec(24)
    >>> v0 = BitVecVal(2, 2)
    >>> v0
    2
    >>> v0.size()
    2
    >>> v  = simplify(ZeroExt(6, v0))
    >>> v
    2
    >>> v.size()
    8
    """
    if debugging():
        _assert(_is_int(n), "First argument must be an integer")
        _assert(is_bv(a), "Second argument must be a Z3 bit-vector expression")
    s = a.ctx.solver
    return BitVecRef(s.mkTerm(s.mkOp(kinds.BVZeroExtend, n), a.ast), a.ctx)


def RepeatBitVec(n, a):
    """Return an expression representing `n` copies of `a`.

    >>> x = BitVec('x', 8)
    >>> n = RepeatBitVec(4, x)
    >>> n
    RepeatBitVec(4, x)
    >>> n.size()
    32
    >>> v0 = BitVecVal(10, 4)
    >>> print("%.x" % v0.as_long())
    a
    >>> v = simplify(RepeatBitVec(4, v0))
    >>> v.size()
    16
    >>> print("%.x" % v.as_long())
    aaaa
    """
    if debugging():
        _assert(_is_int(n), "First argument must be an integer")
        _assert(is_bv(a), "Second argument must be a Z3 bit-vector expression")
    return BitVecRef(
        a.ctx.solver.mkTerm(a.ctx.solver.mkOp(kinds.BVRepeat, n), a.ast), a.ctx
    )


def BVRedAnd(a):
    """Return the reduction-and expression of `a`."""
    if debugging():
        _assert(is_bv(a), "First argument must be a Z3 bit-vector expression")
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVRedand, a.ast), a.ctx)


def BVRedOr(a):
    """Return the reduction-or expression of `a`."""
    if debugging():
        _assert(is_bv(a), "First argument must be a Z3 bit-vector expression")
    return BitVecRef(a.ctx.solver.mkTerm(kinds.BVRedor, a.ast), a.ctx)


def BVAddNoOverflow(a, b, signed):
    """A predicate the determines that bit-vector addition does not overflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    unimplemented()


def BVAddNoUnderflow(a, b):
    """A predicate the determines that signed bit-vector addition does not underflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    unimplemented()


def BVSubNoOverflow(a, b):
    """A predicate the determines that bit-vector subtraction does not overflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    unimplemented()


def BVSubNoUnderflow(a, b, signed):
    """A predicate the determines that bit-vector subtraction does not underflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    unimplemented()


def BVSDivNoOverflow(a, b):
    """A predicate the determines that bit-vector signed division does not overflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    unimplemented()


def BVSNegNoOverflow(a):
    """A predicate the determines that bit-vector unary negation does not overflow"""
    if debugging():
        _assert(is_bv(a), "First argument must be a Z3 bit-vector expression")
    unimplemented()


def BVMulNoOverflow(a, b, signed):
    """A predicate the determines that bit-vector multiplication does not overflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    unimplemented()


def BVMulNoUnderflow(a, b):
    """A predicate the determines that bit-vector signed multiplication does not underflow"""
    _check_bv_args(a, b)
    a, b = _coerce_exprs(a, b)
    unimplemented()


#########################################
#
# Arrays
#
#########################################


class ArraySortRef(SortRef):
    """Array sorts."""

    def domain(self):
        """Return the domain of the array sort `self`.

        >>> A = ArraySort(IntSort(), BoolSort())
        >>> A.domain()
        Int
        """
        return _to_sort_ref(self.ast.getArrayIndexSort(), self.ctx)

    def range(self):
        """Return the range of the array sort `self`.

        >>> A = ArraySort(IntSort(), BoolSort())
        >>> A.range()
        Bool
        """
        return _to_sort_ref(self.ast.getArrayElementSort(), self.ctx)


class ArrayRef(ExprRef):
    """Array expressions."""

    def sort(self):
        """Return the array sort of the array expression `self`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> a.sort()
        Array(Int, Bool)
        """
        return _sort(self.ctx, self.ast)

    def domain(self):
        """Shorthand for `self.sort().domain()`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> a.domain()
        Int
        """
        return self.sort().domain()

    def range(self):
        """Shorthand for `self.sort().range()`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> a.range()
        Bool
        """
        return self.sort().range()

    def __getitem__(self, arg):
        """Return the Z3 expression `self[arg]`.

        >>> a = Array('a', IntSort(), BoolSort())
        >>> i = Int('i')
        >>> a[i]
        a[i]
        >>> a[i].sexpr()
        '(select a i)'
        """
        arg = self.domain().cast(arg)
        return _to_expr_ref(
            self.ctx.solver.mkTerm(kinds.Select, self.ast, arg.ast), self.ctx
        )

    def arg(self, idx):
        """Get the "argument" (base element) of this constant array.

        >>> b = K(IntSort(), 1)
        >>> b.arg(0)
        1
        """
        if debugging():
            _assert(is_app(self), "Z3 application expected")
            _assert(idx < 1, "Invalid argument index")
        return _to_expr_ref(self.ast.getConstArrayBase(), self.ctx)

    def default(self):
        unimplemented()


def is_array_sort(a):
    instance_check(a, SortRef)
    return a.ast.isArray()


def is_array(a):
    """Return `True` if `a` is a Z3 array expression.

    >>> a = Array('a', IntSort(), IntSort())
    >>> is_array(a)
    True
    >>> is_array(Store(a, 0, 1))
    True
    >>> is_array(a[0])
    False
    """
    return isinstance(a, ArrayRef)


def is_const_array(a):
    """Return `True` if `a` is a Z3 constant array.

    >>> a = K(IntSort(), 10)
    >>> is_const_array(a)
    True
    >>> a = Array('a', IntSort(), IntSort())
    >>> is_const_array(a)
    False
    """
    return is_app_of(a, kinds.ConstArray)


def is_K(a):
    """Return `True` if `a` is a Z3 constant array.

    >>> a = K(IntSort(), 10)
    >>> is_K(a)
    True
    >>> a = Array('a', IntSort(), IntSort())
    >>> is_K(a)
    False
    """
    return is_const_array(a)


def ArraySort(*sig):
    """Return the Z3 array sort with the given domain and range sorts.

    >>> A = ArraySort(IntSort(), BoolSort())
    >>> A
    Array(Int, Bool)
    >>> A.domain()
    Int
    >>> A.range()
    Bool
    >>> AA = ArraySort(IntSort(), A)
    >>> AA
    Array(Int, Array(Int, Bool))
    """
    sig = _get_args(sig)
    if debugging():
        _assert(len(sig) > 1, "At least two arguments expected")
    arity = len(sig) - 1
    r = sig[arity]
    d = sig[0]
    if debugging():
        for s in sig:
            _assert(is_sort(s), "Z3 sort expected")
            _assert(s.ctx == r.ctx, "Context mismatch")
    ctx = d.ctx
    if len(sig) == 2:
        return ArraySortRef(ctx.solver.mkArraySort(d.ast, r.ast), ctx)
    else:
        unimplemented("multi-domain array")


def Array(name, dom, rng):
    """Return an array constant named `name` with the given domain and range sorts.

    >>> a = Array('a', IntSort(), IntSort())
    >>> a.sort()
    Array(Int, Int)
    >>> a[0]
    a[0]
    """
    ctx = dom.ctx
    s = ctx.solver.mkArraySort(dom.ast, rng.ast)
    e = ctx.get_var(name, _to_sort_ref(s, ctx))
    return ArrayRef(e, ctx)


def Update(a, i, v):
    """Return a Z3 store array expression.

    >>> a    = Array('a', IntSort(), IntSort())
    >>> i, v = Ints('i v')
    >>> s    = Update(a, i, v)
    >>> s.sort()
    Array(Int, Int)
    >>> prove(s[i] == v)
    proved
    >>> j    = Int('j')
    >>> prove(Implies(i != j, s[j] == a[j]))
    proved
    """
    if debugging():
        _assert(is_array(a), "First argument must be a Z3 array expression")
    i = a.sort().domain().cast(i)
    v = a.sort().range().cast(v)
    ctx = a.ctx
    return _to_expr_ref(ctx.solver.mkTerm(kinds.Store, a.ast, i.ast, v.ast), ctx)


def Store(a, i, v):
    """Return a Z3 store array expression.

    >>> a    = Array('a', IntSort(), IntSort())
    >>> i, v = Ints('i v')
    >>> s    = Store(a, i, v)
    >>> s.sort()
    Array(Int, Int)
    >>> prove(s[i] == v)
    proved
    >>> j    = Int('j')
    >>> prove(Implies(i != j, s[j] == a[j]))
    proved
    """
    return Update(a, i, v)


def Select(a, i):
    """Return a Z3 select array expression.

    >>> a = Array('a', IntSort(), IntSort())
    >>> i = Int('i')
    >>> Select(a, i)
    a[i]
    >>> eq(Select(a, i), a[i])
    True
    """
    if debugging():
        _assert(is_array(a), "First argument must be a Z3 array expression")
    return a[i]


def K(dom, v):
    """Return a Z3 constant array expression.

    >>> a = K(IntSort(), 10)
    >>> a
    K(Int, 10)
    >>> a.sort()
    Array(Int, Int)
    >>> i = Int('i')
    >>> a[i]
    K(Int, 10)[i]
    >>> simplify(a[i])
    10
    """
    if debugging():
        _assert(is_sort(dom), "Z3 sort expected")
    ctx = dom.ctx
    if not is_expr(v):
        v = _py2expr(v, ctx)
    sort = ArraySort(dom, v.sort())
    return ArrayRef(ctx.solver.mkConstArray(sort.ast, v.ast), ctx)


def Ext(a, b):
    """Return extensionality index for one-dimensional arrays.
    >> a, b = Consts('a b', SetSort(IntSort()))
    >> Ext(a, b)
    Ext(a, b)
    """
    unimplemented()


def SetHasSize(a, k):
    unimplemented()


def is_select(a):
    """Return `True` if `a` is a Z3 array select application.

    >>> a = Array('a', IntSort(), IntSort())
    >>> is_select(a)
    False
    >>> i = Int('i')
    >>> is_select(a[i])
    True
    """
    return is_app_of(a, kinds.Select)


def is_store(a):
    """Return `True` if `a` is a Z3 array store application.

    >>> a = Array('a', IntSort(), IntSort())
    >>> is_store(a)
    False
    >>> is_store(Store(a, 0, 1))
    True
    """
    return is_app_of(a, kinds.Store)


#########################################
#
# Sets
#
#########################################


class SetSortRef(SortRef):
    """Array sorts."""

    def domain(self):
        """Return the domain of the set sort `self`.

        >>> A = SetSort(IntSort())
        >>> A.domain()
        Int
        """
        return _to_sort_ref(self.ast.getSetElementSort(), self.ctx)

    def range(self):
        """Return the range of the array sort `self`.
        Included for compatibility with arrays.

        >>> A = SetSort(IntSort())
        >>> A.range()
        Bool
        """
        return BoolSort(self.ctx)


class SetRef(ExprRef):
    """Array expressions."""

    def sort(self):
        """Return the set sort of the set expression `self`.

        >>> a = Set('a', IntSort())
        >>> a.sort()
        Set(Int)
        """
        return _sort(self.ctx, self.ast)

    def domain(self):
        """Shorthand for `self.sort().domain()`.

        >>> a = Set('a', IntSort())
        >>> a.domain()
        Int
        """
        return self.sort().domain()

    def range(self):
        """Shorthand for `self.sort().range()`.
        Included for compatibility with arrays.

        >>> a = Set('a', IntSort())
        >>> a.range()
        Bool
        """
        return self.sort().range()

    def __getitem__(self, arg):
        """Return the Z3 expression `self[arg]`.
        Included for compatibility with arrays.

        >>> a = Set('a', IntSort())
        >>> i = Int('i')
        >>> a[i]
        member(i, a)
        """
        arg = self.domain().cast(arg)
        return _to_expr_ref(
            self.ctx.solver.mkTerm(kinds.Member, arg.ast, self.ast), self.ctx
        )

    def default(self):
        return BoolRef(self.ctx.solver.mkFalse(), self.ctx)


def Set(name, elem_sort):
    """Creates a symbolic set of elements"""
    sort = SetSort(elem_sort)
    ctx = _get_ctx(sort.ctx)
    e = ctx.get_var(name, sort)
    return SetRef(e, ctx)


def SetSort(s):
    """Create a set sort over element sort s"""
    ctx = s.ctx
    instance_check(s, SortRef)
    sort = ctx.solver.mkSetSort(s.ast)
    return SetSortRef(sort, ctx)


def EmptySet(s):
    """Create the empty set
    >>> EmptySet(IntSort())
    Empty(Set(Int))
    """
    ctx = s.ctx
    sort = SetSort(s)
    return SetRef(ctx.solver.mkEmptySet(sort.ast), ctx)


def FullSet(s):
    """Create the full set
    >>> FullSet(IntSort())
    Full(Set(Int))
    """
    ctx = s.ctx
    sort = SetSort(s)
    return SetRef(ctx.solver.mkUniverseSet(sort.ast), ctx)


def SetUnion(*args):
    """Take the union of sets
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetUnion(a, b)
    union(a, b)
    """
    args = _get_args(args)
    ctx = _ctx_from_ast_arg_list(args)
    return SetRef(ctx.solver.mkTerm(kinds.Union, *[a.ast for a in args]), ctx)


def SetIntersect(*args):
    """Take the union of sets
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetIntersect(a, b)
    intersection(a, b)
    """
    args = _get_args(args)
    ctx = _ctx_from_ast_arg_list(args)
    return SetRef(ctx.solver.mkTerm(kinds.Intersection, *[a.ast for a in args]), ctx)


def SetAdd(s, e):
    """Add element e to set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> SetAdd(a, 1)
    insert(a, 1)
    """
    ctx = _ctx_from_ast_arg_list([s, e])
    e = _py2expr(e, ctx)
    return SetRef(ctx.solver.mkTerm(kinds.Insert, e.ast, s.ast), ctx, True)


def SetDel(s, e):
    """Remove element e to set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> SetDel(a, 1)
    setminus(a, singleton(1))
    """
    return SetDifference(s, Singleton(e))


def SetComplement(s):
    """The complement of set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> SetComplement(a)
    complement(a)
    """
    ctx = s.ctx
    return ArrayRef(ctx.solver.mkTerm(kinds.Complement, s.ast), ctx)


def Singleton(s):
    """The single element set of just e
    >>> Singleton(IntVal(1))
    singleton(1)
    """
    s = _py2expr(s)
    ctx = s.ctx
    return SetRef(ctx.solver.mkTerm(kinds.Singleton, s.ast), ctx)


def SetDifference(a, b):
    """The set difference of a and b
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetDifference(a, b)
    setminus(a, b)
    """
    ctx = _ctx_from_ast_arg_list([a, b])
    return SetRef(ctx.solver.mkTerm(kinds.Setminus, a.ast, b.ast), ctx)


def SetMinus(a, b):
    """The set difference of a and b
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> SetMinus(a, b)
    setminus(a, b)
    """
    return SetDifference(a, b)


def IsMember(e, s):
    """Check if e is a member of set s
    >>> a = Const('a', SetSort(IntSort()))
    >>> IsMember(1, a)
    member(1, a)
    """
    ctx = _ctx_from_ast_arg_list([s, e])
    arg = s.domain().cast(e)
    return BoolRef(ctx.solver.mkTerm(kinds.Member, arg.ast, s.ast), ctx)


def IsSubset(a, b):
    """Check if a is a subset of b
    >>> a = Const('a', SetSort(IntSort()))
    >>> b = Const('b', SetSort(IntSort()))
    >>> IsSubset(a, b)
    subset(a, b)
    """
    ctx = _ctx_from_ast_arg_list([a, b])
    return BoolRef(ctx.solver.mkTerm(kinds.Subset, a.ast, b.ast), ctx)


#########################################
#
# Solver
#
#########################################
class CheckSatResult(object):
    """Represents the result of a satisfiability check: sat, unsat, unknown.

    >>> s = Solver()
    >>> s.check()
    sat
    >>> r = s.check()
    >>> isinstance(r, CheckSatResult)
    True
    """

    def __init__(self, r):
        instance_check(r, pc.Result)
        self.r = r

    def __deepcopy__(self, memo={}):
        return CheckSatResult(self.r)

    def __eq__(self, other):
        return repr(self) == repr(other)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __repr__(self):
        if self.r.isSat():
            return "sat"
        elif self.r.isUnsat():
            return "unsat"
        else:
            return "unknown"


class CheckSatResultLiteral(CheckSatResult):
    """Represents the literal result of a satisfiability check: sat, unsat, unknown.

    >>> s = Solver()
    >>> s.check()
    sat
    >>> s.check() == CheckSatResultLiteral("sat")
    True
    """

    def __init__(self, string):
        self.string = string

    def __deepcopy__(self, memo={}):
        return CheckSatResultLiteral(self.string)

    def __repr__(self):
        return self.string


sat = CheckSatResultLiteral("sat")
unsat = CheckSatResultLiteral("unsat")
unknown = CheckSatResultLiteral("unknown")


class Solver(object):
    """Solver API provides methods for implementing the main SMT 2.0 commands: push, pop, check, get-model, etc."""

    def __init__(self, solver=None, ctx=None, logFile=None):
        assert solver is None or ctx is not None
        self.ctx = _get_ctx(ctx)
        self.solver = self.ctx.solver
        self.scopes = 0
        self.assertions_ = [[]]
        self.last_result = None
        self.reset()

    def __del__(self):
        if self.solver is not None and self.ctx.ref() is not None:
            self.ctx = None
            self.solver = None

    def push(self):
        """Create a backtracking point.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s
        [x > 0]
        >>> s.push()
        >>> s.add(x < 1)
        >>> s
        [x > 0, x < 1]
        >>> s.check()
        unsat
        >>> s.pop()
        >>> s.check()
        sat
        >>> s
        [x > 0]
        """
        self.scopes += 1
        self.assertions_.append([])
        self.solver.push(1)

    def pop(self, num=1):
        """Backtrack \c num backtracking points.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s
        [x > 0]
        >>> s.push()
        >>> s.add(x < 1)
        >>> s
        [x > 0, x < 1]
        >>> s.check()
        unsat
        >>> s.pop()
        >>> s.check()
        sat
        >>> s
        [x > 0]
        """
        assert num <= self.scopes
        self.scopes -= num
        for _ in range(num):
            self.assertions_.pop()
        self.solver.pop(num)

    def num_scopes(self):
        """Return the current number of backtracking points.

        >>> s = Solver()
        >>> s.num_scopes()
        0
        >>> s.push()
        >>> s.num_scopes()
        1
        >>> s.push()
        >>> s.num_scopes()
        2
        >>> s.pop()
        >>> s.num_scopes()
        1
        """
        return self.scopes

    def reset(self):
        """Remove all asserted constraints and backtracking points created using `push()`.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s
        [x > 0]
        >>> s.reset()
        >>> s
        []
        """
        self.solver.resetAssertions()
        self.scopes = 0
        self.assertions_ = [[]]

    def assert_exprs(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.assert_exprs(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        args = _get_args(args)
        s = BoolSort(self.ctx)
        for arg in args:
            arg = s.cast(arg)
            self.assertions_[-1].append(arg)
            self.solver.assertFormula(arg.ast)

    def add(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def __iadd__(self, fml):
        self.add(fml)
        return self

    def append(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.append(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def insert(self, *args):
        """Assert constraints into the solver.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.insert(x > 0, x < 2)
        >>> s
        [x > 0, x < 2]
        """
        self.assert_exprs(*args)

    def check(self, *assumptions):
        """Check whether the assertions in the given solver plus the optional assumptions are consistent or not.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.check()
        sat
        >>> s.add(x > 0, x < 2)
        >>> s.check()
        sat
        >>> s.model().eval(x)
        1
        >>> s.add(x < 1)
        >>> s.check()
        unsat
        >>> s.reset()
        """
        assumptions = _get_args(assumptions)
        return CheckSatResult(
            self.solver.checkSatAssuming(*[a.ast for a in assumptions])
        )

    def model(self):
        """Return a model for the last `check()`.

        This function raises an exception if
        a model is not available (e.g., last `check()` returned unsat).

        >>> s = Solver()
        >>> a = Int('a')
        >>> s.add(a + 2 == 0)
        >>> s.check()
        sat
        >>> s.model()
        [a = -2]
        """
        return ModelRef(self, self.ctx)

    def import_model_converter(self, other):
        """Import model converter from other into the current solver"""
        unimplemented()

    def cube(self, vars=None):
        """Get set of cubes
        The method takes an optional set of variables that restrict which
        variables may be used as a starting point for cubing.
        If vars is not None, then the first case split is based on a variable in
        this set.
        """
        unimplemented()

    def cube_vars(self):
        """Access the set of variables that were touched by the most recently generated cube.
        This set of variables can be used as a starting point for additional cubes.
        The idea is that variables that appear in clauses that are reduced by the most recent
        cube are likely more useful to cube on."""
        return self.cube_vs

    def proof(self):
        """Return a proof for the last `check()`. Proof construction must be enabled."""
        unimplemented()

    def assertions(self):
        """Return an AST vector containing all added constraints.

        >>> s = Solver()
        >>> s.assertions()
        []
        >>> a = Int('a')
        >>> s.add(a > 0)
        >>> s.add(a < 10)
        >>> s.assertions()
        [a > 0, a < 10]
        """
        return ft.reduce(op.add, self.assertions_)

    def units(self):
        """Return an AST vector containing all currently inferred units."""
        unimplemented()

    def non_units(self):
        """Return an AST vector containing all atomic formulas in solver state that are not units."""
        unimplemented()

    def trail_levels(self):
        """Return trail and decision levels of the solver state after a check() call."""
        unimplemented()

    def trail(self):
        """Return trail of the solver state after a check() call."""
        unimplemented()

    def reason_unknown(self):
        """Return a string describing why the last `check()` returned `unknown`.

        >>> x = Int('x')
        >>> s = SimpleSolver()
        """
        _assert(
            self.last_result is not None,
            "No previous check-sat call, so no reason for unknown",
        )
        return self.last_result.r.getUnknownExplanation()

    def help(self):
        """Display a string describing all available options."""
        unimplemented()

    def param_descrs(self):
        """Return the parameter description set."""
        unimplemented()

    def __repr__(self):
        """Return a formatted string with all added constraints."""
        return "[" + ", ".join(str(a) for a in self.assertions()) + "]"

    def sexpr(self):
        """Return a formatted string (in Lisp-like format) with all added constraints. We say the string is in s-expression format.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0)
        >>> s.add(x < 2)
        >>> r = s.sexpr()
        """
        return "(and " + " ".join(a.sexpr() for a in self.assertions()) + ")"

    def dimacs(self, include_names=True):
        """Return a textual representation of the solver in DIMACS format."""
        unimplemented()

    def to_smt2(self):
        """return SMTLIB2 formatted benchmark for solver's assertions"""
        unimplemented()


def SolverFor(logic, ctx=None, logFile=None):
    """Create a solver customized for the given logic.

    The parameter `logic` is a string. It should be contains
    the name of a SMT-LIB logic.
    See http://www.smtlib.org/ for the name of all available logics.

    >>> s = SolverFor("QF_LIA")
    >>> x = Int('x')
    >>> s.add(x > 0)
    >>> s.add(x < 2)
    >>> s.check()
    sat
    >>> s.model()
    [x = 1]
    """
    solver = pc.Solver()
    solver.setLogic(logic)
    ctx = _get_ctx(ctx)
    return Solver(solver, ctx, logFile)


def SimpleSolver(ctx=None, logFile=None):
    """Return a simple general purpose solver with limited amount of preprocessing.

    >>> s = SimpleSolver()
    >>> x = Int('x')
    >>> s.add(x > 0)
    >>> s.check()
    sat
    """
    ctx = _get_ctx(ctx)
    return Solver(None, ctx, logFile)


#########################################
#
# Utils
#
#########################################


def substitute(t, *m):
    """Apply substitution m on t, m is a list of pairs of the form (from, to). Every occurrence in t of from is replaced with to.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> # substitute(x + 1, (x, y + 1))
    >>> f = Function('f', IntSort(), IntSort())
    >>> substitute(f(x) + f(y), (f(x), IntVal(1)), (f(y), IntVal(1)))
    1 + 1
    """
    if isinstance(m, tuple):
        m1 = _get_args(m)
        if isinstance(m1, list) and all(isinstance(p, tuple) for p in m1):
            m = m1
    if debugging():
        _assert(is_expr(t), "Z3 expression expected")
        _assert(
            all(
                [
                    isinstance(p, tuple)
                    and is_expr(p[0])
                    and is_expr(p[1])
                    and p[0].sort().eq(p[1].sort())
                    for p in m
                ]
            ),
            "Z3 invalid substitution, expression pairs expected.",
        )
    num = len(m)
    froms = []
    tos = []
    for i in range(num):
        froms.append(m[i][0].ast)
        tos.append(m[i][1].ast)
    return _to_expr_ref(t.ast.substitute(froms, tos), t.ctx)


def Sum(*args):
    """Create the sum of the Z3 expressions.

    >>> a, b, c = Ints('a b c')
    >>> Sum(a, b, c)
    a + b + c
    >>> Sum([a, b, c])
    a + b + c
    >>> A = IntVector('a', 5)
    >>> Sum(A)
    a__0 + a__1 + a__2 + a__3 + a__4
    """
    args = _get_args(args)
    if len(args) == 0:
        return 0
    ctx = _ctx_from_ast_arg_list(args)
    if ctx is None:
        return _reduce(lambda a, b: a + b, args, 0)
    args = _coerce_expr_list(args, ctx)
    if is_bv(args[0]):
        return _reduce(lambda a, b: a + b, args, 0)
    else:
        return ArithRef(ctx.solver.mkTerm(kinds.Plus, *[a.ast for a in args]), ctx)


def Product(*args):
    """Create the product of the Z3 expressions.

    >>> a, b, c = Ints('a b c')
    >>> Product(a, b, c)
    a*b*c
    >>> Product([a, b, c])
    a*b*c
    >>> A = IntVector('a', 5)
    >>> Product(A)
    a__0*a__1*a__2*a__3*a__4
    """
    args = _get_args(args)
    if len(args) == 0:
        return 1
    ctx = _ctx_from_ast_arg_list(args)
    if ctx is None:
        return ft.reduce(lambda a, b: a * b, args)
    args = _coerce_expr_list(args, ctx)
    if is_bv(args[0]):
        return ft.reduce(lambda a, b: a * b, args)
    else:
        return ArithRef(ctx.solver.mkTerm(kinds.Mult, *[a.ast for a in args]), ctx)


# def AtMost(*args):
#     """Create an at-most Pseudo-Boolean k constraint.
#
#     >>> a, b, c = Bools('a b c')
#     >>> f = AtMost(a, b, c, 2)
#     """
#     unimplemented()
#
#
# def AtLeast(*args):
#     """Create an at-most Pseudo-Boolean k constraint.
#
#     >>> a, b, c = Bools('a b c')
#     >>> f = AtLeast(a, b, c, 2)
#     """
#     unimplemented()
#
#
# def PbLe(args, k):
#     """Create a Pseudo-Boolean inequality k constraint.
#
#     >>> a, b, c = Bools('a b c')
#     >>> f = PbLe(((a,1),(b,3),(c,2)), 3)
#     """
#     unimplemented()
#
#
# def PbGe(args, k):
#     """Create a Pseudo-Boolean inequality k constraint.
#
#     >>> a, b, c = Bools('a b c')
#     >>> f = PbGe(((a,1),(b,3),(c,2)), 3)
#     """
#     unimplemented()
#
#
# def PbEq(args, k, ctx=None):
#     """Create a Pseudo-Boolean inequality k constraint.
#
#     >>> a, b, c = Bools('a b c')
#     >>> f = PbEq(((a,1),(b,3),(c,2)), 3)
#     """
#     unimplemented()


def solve(*args, **keywords):
    """Solve the constraints `*args`.

    This is a simple function for creating demonstrations. It creates a solver,
    configure it using the options in `keywords`, adds the constraints
    in `args`, and invokes check.

    >>> a = Int('a')
    >>> solve(a > 0, a < 2)
    [a = 1]
    """
    s = Solver()
    s.add(*args)
    if keywords.get("show", False):
        print(s)
    r = s.check()
    if r == unsat:
        print("no solution")
    elif r == unknown:
        print("failed to solve")
        try:
            print(s.model())
        except Z3Exception:
            return
    else:
        m = s.model()
        print(m)


def solve_using(s, *args, **keywords):
    """Solve the constraints `*args` using solver `s`.

    This is a simple function for creating demonstrations. It is similar to `solve`,
    but it uses the given solver `s`.
    It configures solver `s` using the options in `keywords`, adds the constraints
    in `args`, and invokes check.
    """
    if debugging():
        _assert(isinstance(s, Solver), "Solver object expected")
    s.set(**keywords)
    s.add(*args)
    if keywords.get("show", False):
        print("Problem:")
        print(s)
    r = s.check()
    print(r)
    print(unsat == r)
    if r == unsat:
        print("no solution")
    elif r == unknown:
        print("failed to solve")
        try:
            print(s.model())
        except Z3Exception:
            return
    else:
        if keywords.get("show", False):
            print("Solution:")
        print(s.model())


def prove(claim, **keywords):
    """Try to prove the given claim.

    This is a simple function for creating demonstrations.  It tries to prove
    `claim` by showing the negation is unsatisfiable.

    >>> p, q = Bools('p q')
    >>> prove(Not(And(p, q)) == Or(Not(p), Not(q)))
    proved
    """
    if debugging():
        _assert(is_bool(claim), "Z3 Boolean expression expected")
    s = Solver()
    s.add(Not(claim))
    if keywords.get("show", False):
        print(s)
    r = s.check()
    if r == unsat:
        print("proved")
    elif r == unknown:
        print("failed to prove")
        print(s.model())
    else:
        print("counterexample")
        print(s.model())


def _solve_html(*args, **keywords):
    """Version of function `solve` used in RiSE4Fun."""
    s = Solver()
    s.set(**keywords)
    s.add(*args)
    if keywords.get("show", False):
        print("<b>Problem:</b>")
        print(s)
    r = s.check()
    if r == unsat:
        print("<b>no solution</b>")
    elif r == unknown:
        print("<b>failed to solve</b>")
        try:
            print(s.model())
        except Z3Exception:
            return
    else:
        if keywords.get("show", False):
            print("<b>Solution:</b>")
        print(s.model())


def _solve_using_html(s, *args, **keywords):
    """Version of function `solve_using` used in RiSE4Fun."""
    if debugging():
        _assert(isinstance(s, Solver), "Solver object expected")
    s.set(**keywords)
    s.add(*args)
    if keywords.get("show", False):
        print("<b>Problem:</b>")
        print(s)
    r = s.check()
    if r == unsat:
        print("<b>no solution</b>")
    elif r == unknown:
        print("<b>failed to solve</b>")
        try:
            print(s.model())
        except Z3Exception:
            return
    else:
        if keywords.get("show", False):
            print("<b>Solution:</b>")
        print(s.model())


def _prove_html(claim, **keywords):
    """Version of function `prove` used in RiSE4Fun."""
    if debugging():
        _assert(is_bool(claim), "Z3 Boolean expression expected")
    s = Solver()
    s.set(**keywords)
    s.add(Not(claim))
    if keywords.get("show", False):
        print(s)
    r = s.check()
    if r == unsat:
        print("<b>proved</b>")
    elif r == unknown:
        print("<b>failed to prove</b>")
        print(s.model())
    else:
        print("<b>counterexample</b>")
        print(s.model())


def _dict2sarray(sorts, ctx):
    sz = len(sorts)
    _names = (Symbol * sz)()
    _sorts = (Sort * sz)()
    i = 0
    for k in sorts:
        v = sorts[k]
        if debugging():
            _assert(isinstance(k, str), "String expected")
            _assert(is_sort(v), "Z3 sort expected")
        _names[i] = to_symbol(k, ctx)
        _sorts[i] = v.ast
        i = i + 1
    return sz, _names, _sorts


def _dict2darray(decls, ctx):
    sz = len(decls)
    _names = (Symbol * sz)()
    _decls = (FuncDecl * sz)()
    i = 0
    for k in decls:
        v = decls[k]
        if debugging():
            _assert(isinstance(k, str), "String expected")
            _assert(
                is_func_decl(v) or is_const(v), "Z3 declaration or constant expected"
            )
        _names[i] = to_symbol(k, ctx)
        if is_const(v):
            _decls[i] = v.decl().ast
        else:
            _decls[i] = v.ast
        i = i + 1
    return sz, _names, _decls


def parse_smt2_file(f, sorts={}, decls={}, ctx=None):
    """Parse a file in SMT 2.0 format using the given sorts and decls.

    This function is similar to parse_smt2_string().
    """
    unimplemented()


class ModelRef:
    """Model/Solution of a satisfiability problem (aka system of constraints)."""

    def __init__(self, solver, ctx):
        assert solver is not None
        assert ctx is not None
        self.solver = solver
        self.ctx = ctx

    def __del__(self):
        if self.solver is not None:
            self.solver = None
        if self.ctx is not None:
            self.ctx = None

    def vars(self):
        """Returns the free constants in an assertion, as terms"""
        visit = {a: True for a in self.solver.assertions()}
        q = list(visit.keys())
        vars_ = set()
        while len(q) > 0:
            a = q.pop()
            if a.ast.getKind() == kinds.Constant:
                vars_.add(a)
            else:
                for c in a.children():
                    if c not in visit:
                        visit[c] = True
                        q.append(c)
                if a.kind() == kinds.ApplyUf:
                    c = a.decl()
                    if c not in visit:
                        visit[c] = True
                        q.append(c)

        return vars_

    def __repr__(self):
        var_vals = [(str(v), self[v]) for v in self.decls()]
        inner = ", ".join(
            v + " = " + str(val) for v, val in sorted(var_vals, key=lambda a: a[0])
        )
        return "[" + inner + "]"

    def sexpr(self):
        """Return a textual representation of the s-expression representing the model."""
        unimplemented()

    def eval(self, t, model_completion=False):
        """Evaluate the expression `t` in the model `self`. If `model_completion` is enabled, then a default interpretation is automatically added for symbols that do not have an interpretation in the model `self`.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.eval(x + 1)
        2
        >>> m.eval(x == 1)
        True
        """
        return _to_expr_ref(self.solver.solver.getValue(t.ast), self.solver.ctx)

    def evaluate(self, t, model_completion=False):
        """Alias for `eval`.

        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.evaluate(x + 1)
        2
        >>> m.evaluate(x == 1)
        True
        """
        return self.eval(t, model_completion)

    def __len__(self):
        """Return the number of constant and function declarations in the model `self`.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, f(x) != x)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> len(m)
        2
        """
        return len(self.decls())

    def get_interp(self, decl):
        """Return the interpretation for a given declaration or constant.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2, f(x) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m[x]
        1
        """
        unimplemented()

    def num_sorts(self):
        """Return the number of uninterpreted sorts that contain an interpretation in the model `self`.

        >>> A = DeclareSort('A')
        >>> a, b = Consts('a b', A)
        >>> s = Solver()
        >>> s.add(a != b)
        >>> s.check()
        sat
        >>> m = s.model()
        """
        unimplemented()

    def get_sort(self, idx):
        """Return the uninterpreted sort at position `idx` < self.num_sorts().

        >>> A = DeclareSort('A')
        >>> B = DeclareSort('B')
        >>> a1, a2 = Consts('a1 a2', A)
        >>> b1, b2 = Consts('b1 b2', B)
        >>> s = Solver()
        >>> s.add(a1 != a2, b1 != b2)
        >>> s.check()
        sat
        >>> m = s.model()
        """
        unimplemented()

    def sorts(self):
        """Return all uninterpreted sorts that have an interpretation in the model `self`.

        >>> A = DeclareSort('A')
        >>> B = DeclareSort('B')
        >>> a1, a2 = Consts('a1 a2', A)
        >>> b1, b2 = Consts('b1 b2', B)
        >>> s = Solver()
        >>> s.add(a1 != a2, b1 != b2)
        >>> s.check()
        sat
        >>> m = s.model()
        """
        unimplemented()

    def get_universe(self, s):
        """Return the interpretation for the uninterpreted sort `s` in the model `self`.

        >>> A = DeclareSort('A')
        >>> a, b = Consts('a b', A)
        >>> s = Solver()
        >>> s.add(a != b)
        >>> s.check()
        sat
        >>> m = s.model()
        """
        unimplemented()

    def __getitem__(self, idx):
        """If `idx` is an integer, then the declaration at position `idx` in the model `self` is returned. If `idx` is a declaration, then the actual interpretation is returned.

        The elements can be retrieved using position or the actual declaration.

        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2, f(x) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.decls()
        [f, x]
        >>> len(m)
        2
        >>> m[0]
        f
        >>> m[1]
        x
        >>> m[x]
        1
        """
        if _is_int(idx):
            return self.decls()[idx]
        if isinstance(idx, ExprRef):
            return self.eval(idx)
        if isinstance(idx, SortRef):
            unimplemented()
        if debugging():
            _assert(False, "Integer, Z3 declaration, or Z3 constant expected")
        return None

    def decls(self):
        """Return a list with all symbols that have an interpretation in the model `self`.
        >>> f = Function('f', IntSort(), IntSort())
        >>> x = Int('x')
        >>> s = Solver()
        >>> s.add(x > 0, x < 2, f(x) == 0)
        >>> s.check()
        sat
        >>> m = s.model()
        >>> m.decls()
        [f, x]
        """
        return sorted(self.vars(), key=lambda v: str(v))


def evaluate(t):
    """Evaluates the given term (assuming it is constant!)"""
    s = Solver()
    s.check()
    m = s.model()
    return m[t]


def simplify(a):
    """Simplify the expression `a`.

    >>> x = Int('x')
    >>> y = Int('y')
    >>> simplify(x + 1 + y + x + 1)
    2 + 2*x + y
    """
    if debugging():
        _assert(is_expr(a), "Z3 expression expected")
    instance_check(a, ExprRef)
    return _to_expr_ref(a.ctx.solver.simplify(a.ast), a.ctx)
