from __future__ import annotations

from abc import abstractmethod
import functools
from typing import Any, Callable, Generic, Iterator, Optional, Self, TypeVar
from typing_extensions import TypeIs

from ..support.tracing import trace  # noqa


α = TypeVar('α', bound='AtomicFormula')
"""A type variable denoting a type of atomic formulas with upper bound
:class:`deesi.firstorder.atomic.AtomicFormula`.
"""

τ = TypeVar('τ', bound='Term')
"""A type variable denoting a type of terms with upper bound
:class:`deesi.firstorder.atomic.Term`.
"""

χ = TypeVar('χ', bound='Variable')
"""A type variable denoting a type of variables with upper bound
:class:`deesi.firstorder.atomic.Variable`.
"""

σ = TypeVar('σ')
"""A type variable denoting a type admissible as a dictionary entry in
:meth:`.subs`, in addition to terms. Instances of type :data:`.σ` that are
passed to :meth:`.subs` must not contain any variables. A typical example
is :data:`σ` == :class:`int` in the theory of real closed fields.
"""


@functools.total_ordering
class Formula(Generic[α, τ, χ, σ]):
    r"""This abstract base class implements representations of and methods on
    first-order formulas recursively built using first-order operators:

    1. Boolean operators:

       a. Truth values :math:`\top` and :math:`\bot`

       b. Negation :math:`\lnot`

       c. Conjunction :math:`\land` and discjunction :math:`\lor`

       d. Implication :math:`\longrightarrow`

       e. Bi-implication (syntactic equivalence) :math:`\longleftrightarrow`

    2. Quantifiers :math:`\exists x` and :math:`\forall x`, where :math:`x` is
       a variable.

    As an abstract base class, :class:`Formula` cannot be instantiated.
    Nevertheless, it implements a number of methods on first-order formualas.
    The methods implemented here  are typically syntactic in the sense that
    they do not need to know the semantics of the underlying theories.

    .. note::

        :class:`Formula` depends on three type variables :data:`.α`,
        :data:`.τ`, :data:`.χ` for the types ocurring atomic formula, terms,
        and variables, respectively. They appear in type annotations used
        by static type checkers but are not relevant for the either
        interactive use or use as a library.
    """

    _hash: Optional[int]

    @property
    def op(self) -> type[Self]:
        """Operator. This property can be used with instances of subclasses of
        :class:`Formula`. It yields the respective subclass.
        """
        return type(self)

    @property
    def args(self) -> tuple[Any, ...]:
        """The arguments of a formula as a tuple.

        .. seealso::
            * :attr:`Equivalent.lhs <.boolean.Equivalent.lhs>` \
                -- left hand side of a logical :math:`\\longleftrightarrow`
            * :attr:`Equivalent.rhs <.boolean.Equivalent.lhs>` \
                -- right hand side of a logical :math:`\\longleftrightarrow`
            * :attr:`Implies.lhs <.boolean.Equivalent.lhs>` \
                -- left hand side of a logical :math:`\\longrightarrow`
            * :attr:`Implies.rhs <.boolean.Equivalent.lhs>` \
                -- right hand side of a logical :math:`\\longrightarrow`
            * :attr:`Not.arg <.boolean.Not.arg>` \
                -- argument formula of a logical :math:`\\neg`
            * :attr:`QuantifiedFormula.arg <.quantified.QuantifiedFormula.arg>` \
                -- argument formula of a quantifier :math:`\\exists` or \
                :math:`\\forall`
            * :attr:`QuantifiedFormula.var <.quantified.QuantifiedFormula.var>` \
                -- variable of a quantifier :math:`\\exists` or :math:`\\forall`
        """
        return self._args

    @args.setter
    def args(self, args: tuple[Any, ...]) -> None:
        self._args = args

    def __eq__(self, other: object) -> bool:
        """A recursive test for equality of the `self` and `other`.

        Note that this is not a logical operator for equality.

        >>> from deesi.theories.RCF import Ne
        >>>
        >>> e1 = Ne(1, 0)
        >>> e2 = Ne(1, 0)
        >>> e1 == e2
        True
        >>> e1 is e2
        False
        """
        if self is other:
            return True
        if not isinstance(other, Formula):
            return False
        if self.op is not other.op:
            return False
        if hash(self) != hash(other):
            return False
        return self.args == other.args

    def __hash__(self) -> int:
        """
        Hash function.

        hash() yields deterministic results for a fixed hash seed. Set the
        environment variable PYTHONHASHSEED to a positive integer when
        comparing hashes from various Python sessions, e.g. for debugging.
        Recall from the Python documentation that PYTHONHASHSEED should not be
        fixed in general.
        """
        if self._hash is None:
            self._hash = hash((tuple(str(cls) for cls in self.op.mro()), self.args))
        return self._hash

    @abstractmethod
    def __init__(self, *args: object) -> None:
        """This abstract base class is not supposed to have instances itself.
        Technically this is enforced via this abstract initializer.
        """
        self._hash = None

    def __le__(self, other: Formula[α, τ, χ, σ]) -> bool:
        """Returns :external:obj:`True` if `self` should be sorted before or is
        equal to other.

        .. seealso::
          * :meth:`AtomicFormula.__le__() <.firstorder.atomic.AtomicFormula.__le__>`\
             -- comparison of atomic formulas
        """
        L = (And, Or, Not, Implies, Equivalent, Ex, All, _T, _F)
        # The case "self: AtomicFormula" is caught by the implementation of the
        # abstract method AtomicFormula.__le__:
        assert isinstance(self, L)
        if isinstance(other, L):
            if self.op != other.op:
                return L.index(self.op) < L.index(other.op)
            return self.args <= other.args
        # The following is a milder reference to AtomicFormula than the
        # original code:
        assert isinstance(other, AtomicFormula)
        return False

    def __repr__(self) -> str:
        """A Representation of the :class:`Formula` `self` that is suitable for
        use as an input.
        """
        r = self.op.__name__
        r += '('
        if self.args:
            r += self.args[0].__repr__()
            for a in self.args[1:]:
                r += ', ' + a.__repr__()
        r += ')'
        return r

    def as_redlog(self) -> str:
        r"""Redlog representation as a string, which can be used elsewhere.
        """
        match self:
            case All():
                return f'all({self.var}, {self.arg.as_redlog()})'
            case Ex():
                return f'ex({self.var}, {self.arg.as_redlog()})'
            case And():
                return '(' + ' and '.join(arg.as_redlog() for arg in self.args) + ')'
            case Or():
                return '(' + ' or '.join(arg.as_redlog() for arg in self.args) + ')'
            case Implies():
                return f'({self.lhs.as_redlog()} impl {self.rhs.as_redlog()})'
            case Equivalent():
                return f'({self.lhs.as_redlog()} equiv {self.rhs.as_redlog()})'
            case Not():
                return f'not {self.arg.as_redlog()}'
            case _F():
                return 'false'
            case _T():
                return 'true'
            case _:
                # Atomic formulas are caught by the implementation of the
                # abstract method AtomicFormula.as_redlog.
                assert False

    def atoms(self) -> Iterator[α]:
        """
        An iterator over all instances of :class:`AtomicFormula
        <.firstorder.atomic.AtomicFormula>` occurring in `self`.

        Recall that the truth values :data:`T <.boolean.T>` and :data:`F
        <.boolean.F>` are not atoms:

        >>> from deesi.theories.RCF import *
        >>> x, y, z = VV.get('x', 'y', 'z')
        >>> f = Or(And(x == 0, y == 0, T), And(x == 0, y == z, z != 0))
        >>> list(f.atoms())
        [x == 0, y == 0, x == 0, y - z == 0, z != 0]

        The overall number of atoms:

        >>> sum(1 for _ in f.atoms())
        5

        Count numbers of occurrences for each occurring atom using a
        :external+python:class:`Counter <collections.Counter>`:

        >>> from collections import Counter
        >>> Counter(f.atoms())
        Counter({x == 0: 2, y == 0: 1, y - z == 0: 1, z != 0: 1})

        Recall the Python builtin :func:`next`:

        >>> iter = (x == 0).atoms()
        >>> next(iter)
        x == 0
        >>> next(iter)
        Traceback (most recent call last):
        ...
        StopIteration
        """
        match self:
            case All() | Ex():
                yield from self.arg.atoms()
            case And() | Or() | Not() | Implies() | Equivalent() | _F() | _T():
                for arg in self.args:
                    yield from arg.atoms()
            case _:
                # Atomic formulas are caught by the final method
                # AtomicFormula.atoms.
                assert False, type(self)

    def depth(self) -> int:
        """The depth of a formula is the maximal length of a path from the root
        to a truth value or an :class:`AtomicFormula
        <.firstorder.atomic.AtomicFormula>` in the expression tree:

        >>> from deesi.theories.RCF import *
        >>> x, y, z = VV.get('x', 'y', 'z')
        >>> f = Ex(x, And(x == y, All(x, Ex(y, Ex(z, x == y + 1)))))
        >>> f.depth()
        5

        In this example the the following path has the maximal length 5::

            Ex ———— And ———— All ———— Ex ———— Ex ———— x == y + 1

        Note that for this purpose truth values and :class:`AtomicFormula
        <.firstorder.atomic.AtomicFormula>` are considered to have depth 0.
        """
        match self:
            case All() | Ex():
                return self.arg.depth() + 1
            case And() | Or() | Not() | Implies() | Equivalent():
                return max(arg.depth() for arg in self.args) + 1
            case _F() | _T() | AtomicFormula():
                return 0
            case _:
                assert False, type(self)

    def fvars(self, quantified: frozenset[χ] = frozenset()) -> Iterator[χ]:
        """An iterator over all free occurrences of variables in `self`. Each
        variable is reported once for each term that it occurs in.

        The parameter `quantified` specifies variable to be considered bound in
        addition to those that are explicitly quantified in `self`.

        >>> from deesi.theories.RCF import *
        >>> a, x, y, z = VV.get('a', 'x', 'y', 'z')
        >>> f = All(y, And(Ex(x, a + x - y == 0), Ex(z, x + y == a)))
        >>> list(f.fvars())
        [a, a, x]

        .. seealso::
            * :meth:`bvars` -- all occurring bound variables
            * :meth:`qvars` -- all quantified variables
            * :meth:`Term.vars() <.firstorder.atomic.Term.vars>` -- all occurring variables
        """
        match self:
            case All() | Ex():
                yield from self.arg.fvars(quantified.union({self.var}))
            case And() | Or() | Not() | Implies() | Equivalent() | _F() | _T():
                for arg in self.args:
                    yield from arg.fvars(quantified)
            case _:
                assert False, type(self)

    @staticmethod
    def is_all(f: Formula[α, τ, χ, σ]) -> TypeIs[All[α, τ, χ, σ]]:
        """Type narrowing :func:`isinstance` test for :class:`.quantified.All`.
        """
        return isinstance(f, All)

    @staticmethod
    def is_and(f: Formula[α, τ, χ, σ]) -> TypeIs[And[α, τ, χ, σ]]:
        """Type narrowing :func:`isinstance` test for :class:`.boolean.And`.
        """
        return isinstance(f, And)

    @staticmethod
    def is_atomic(f: Formula[α, τ, χ, σ]) -> TypeIs[α]:
        """Type narrowing :func:`isinstance` test for
        :class:`.first-order.atomic.AtomicFormula`.
        """
        return isinstance(f, AtomicFormula)

    @staticmethod
    def is_boolean_formula(f: Formula[α, τ, χ, σ]) -> TypeIs[BooleanFormula[α, τ, χ, σ]]:
        """Type narrowing :func:`isinstance` test for
        :class:`.boolean.BooleanFormula`.
        """
        return isinstance(f, BooleanFormula)

    @staticmethod
    def is_equivalent(f: Formula[α, τ, χ, σ]) -> TypeIs[Equivalent[α, τ, χ, σ]]:
        """Type narrowing :func:`isinstance` test for
        :class:`.boolean.Equivalent`.
        """
        return isinstance(f, Equivalent)

    @staticmethod
    def is_ex(f: Formula[α, τ, χ, σ]) -> TypeIs[Ex[α, τ, χ, σ]]:
        """Type narrowing :func:`isinstance` test for :class:`.quantified.Ex`.
        """
        return isinstance(f, Ex)

    @staticmethod
    def is_false(f: Formula[α, τ, χ, σ]) -> TypeIs[_F[α, τ, χ, σ]]:
        """Type narrowing :func:`isinstance` test for :class:`.boolean._F`.
        """
        return isinstance(f, _F)

    @staticmethod
    def is_implies(f: Formula[α, τ, χ, σ]) -> TypeIs[Implies[α, τ, χ, σ]]:
        """Type narrowing :func:`isinstance` test for
        :class:`.boolean.Implies`.
        """
        return isinstance(f, Implies)

    @staticmethod
    def is_not(f: Formula[α, τ, χ, σ]) -> TypeIs[Not[α, τ, χ, σ]]:
        """Type narrowing :func:`isinstance` test for :class:`.boolean.Not`.
        """
        return isinstance(f, Not)

    @staticmethod
    def is_or(f: Formula[α, τ, χ, σ]) -> TypeIs[Or[α, τ, χ, σ]]:
        """Type narrowing :func:`isinstance` test for :class:`.boolean.Or`.
        """
        return isinstance(f, Or)

    @staticmethod
    def is_quantified_formula(f: Formula[α, τ, χ, σ]) -> TypeIs[QuantifiedFormula[α, τ, χ, σ]]:
        """Type narrowing :func:`isinstance` test for
        :class:`.quantified.QuantifiedFormula`.
        """
        return isinstance(f, QuantifiedFormula)

    @staticmethod
    def is_true(f: Formula[α, τ, χ, σ]) -> TypeIs[_T[α, τ, χ, σ]]:
        """Type narrowing :func:`isinstance` test for :class:`.boolean._T`.
        """
        return isinstance(f, _T)

    @staticmethod
    def is_term(t: τ | σ) -> TypeIs[τ]:
        """Type narrowing :func:`isinstance` test for
        :class:`.firstorder.atomic.Term`.
        """
        return isinstance(t, Term)

    def qvars(self) -> Iterator[χ]:
        """An iterator over all quantified variables in `self`.

        In the following example, ``z`` is a quantified variable but not a
        bound variable:

        >>> from deesi.theories.RCF import *
        >>> a, b, c, x, y, z = VV.get('a', 'b', 'c', 'x', 'y', 'z')
        >>> f = All(y, And(Ex(x, a == y), Ex(z, a == y)))
        >>> list(f.qvars())
        [y, x, z]

        .. seealso::
            * :meth:`bvars` -- all occurring bound variables
            * :meth:`fvars` -- all occurring free variables
            * :meth:`Term.vars() <.firstorder.atomic.Term.vars>` -- all occurring variables
        """
        match self:
            case All() | Ex():
                yield self.var
                yield from self.arg.qvars()
            case And() | Or() | Not() | Implies() | Equivalent() | _F() | _T():
                for arg in self.args:
                    yield from arg.qvars()
            case AtomicFormula():
                yield from ()
            case _:
                assert False, type(self)

    def simplify(self) -> Formula[α, τ, χ, σ]:
        """Fast basic simplification. The result is equivalent to `self`. The
        following first-order simplifications are applied:

        1. Truth values:

           a. Evaluate ``Not(F)`` to ``T``, and evaluate ``Not(T)`` to ``F``.

           b. Evaluate ``And(..., F, ...)`` to ``F`` and ``Or(..., T, ...)`` to
              ``T``.

           c. Evaluate ``Implies(F, arg)`` and ``Implies(arg, T)`` to ``T``.

           d. Remove ``T`` from ``And(..., T, ...)`` and ``F`` from ``Or(...,
              F, ...)``.

           e. Transform ``Implies(T, arg)`` into ``arg``, and transform
              ``Implies(arg, F)`` into ``Not(arg)``.

           f. Transform ``Equivalent(T, arg)`` and ``Equivalent(arg, T)`` into
              ``arg``, and transform ``Equivalent(F, arg)``, ``Equivalent(arg,
              F)`` into ``Not(arg)``.

        2. Nested operators:

           a. Transform ``Not(Not(arg))`` into ``arg``.

           b. Transform ``And(..., And(*args), ...)`` into ``And(..., *args,
              ...)``. The same for ``Or`` instead of ``And``.

        3. Equal arguments:

           a. Transform ``And(..., arg, ..., arg, ...)`` into ``And(..., arg,
              ...)``. The same for ``Or`` instead of ``And``.

           b. Evaluate ``Implies(arg, arg)`` to ``T``. The same for
              ``Equivalent`` instead of ``Implies``.

        4. Sort ``arg_1, ..., arg_n`` within ``And(arg_1, ..., arg_n)`` using a
           canonical order. The same for ``Or`` instead of ``And``.

        Overloading of :class:`AtomicFormula
        <.firstorder.atomic.AtomicFormula>` provides a hook for theories to
        extend :meth:`simplify` to atomic formulas.

        .. seealso::
           `simplify` methods of classes derived from :class:`AtomicFormula
           <.firstorder.atomic.AtomicFormula>` within various theories:

           * :meth:`RCF.atomic.AtomicFormula.simplify
             <deesi.theories.RCF.atomic.AtomicFormula.simplify>` \
            -- real closed fields
           * :meth:`Sets.atomic.AtomicFormula.simplify
             <deesi.theories.Sets.atomic.AtomicFormula.simplify>` \
            -- theory of Sets

           More powerful simplifiers provided by various theories:

           * :func:`RCF.simplify.simplify() \
             <deesi.theories.RCF.simplify.simplify>`
                -- real closed fields, standard simplifier based on implicit theories
           * :func:`Sets.simplify.simplify() \
              <deesi.theories.Sets.simplify.simplify>`
                -- sets, standard simplifier based on implicit theories
        """
        match self:
            case _F() | _T():
                return self
            case Not():
                arg_simplify = self.arg.simplify()
                if arg_simplify is _T():
                    return _F()
                if arg_simplify is _F():
                    return _T()
                return involutive_not(arg_simplify)
            case And() | Or():
                simplified_args: list[Formula] = []
                for arg in self.args:
                    arg_simplify = arg.simplify()
                    if arg_simplify is self.definite_element():
                        return self.definite_element()
                    if arg_simplify is self.neutral_element():
                        continue
                    if arg_simplify in simplified_args:
                        continue
                    if arg_simplify.op is self.op:
                        simplified_args.extend(arg_simplify.args)
                    else:
                        simplified_args.append(arg_simplify)
                return self.op(*simplified_args)
            case Implies():
                if self.rhs is _T():
                    return self.lhs
                lhs_simplify = self.lhs.simplify()
                if lhs_simplify is _F():
                    return _T()
                rhs_simplify = self.rhs.simplify()
                if rhs_simplify is _T():
                    return _T()
                if lhs_simplify is _T():
                    return rhs_simplify
                if rhs_simplify is _F():
                    return involutive_not(lhs_simplify)
                assert {lhs_simplify, rhs_simplify}.isdisjoint({_T(), _F()})
                if lhs_simplify == rhs_simplify:
                    return _T()
                return Implies(lhs_simplify, rhs_simplify)
            case Equivalent():
                lhs_simplify = self.lhs.simplify()
                rhs_simplify = self.rhs.simplify()
                if lhs_simplify is _T():
                    return rhs_simplify
                if rhs_simplify is _T():
                    return lhs_simplify
                if lhs_simplify is _F():
                    if isinstance(rhs_simplify, Not):
                        return rhs_simplify.arg
                    return Not(rhs_simplify)
                if rhs_simplify is _F():
                    if isinstance(lhs_simplify, Not):
                        return lhs_simplify.arg
                    return Not(lhs_simplify)
                if lhs_simplify == rhs_simplify:
                    return _T()
                return Equivalent(lhs_simplify, rhs_simplify)
            case All() | Ex():
                return self.op(self.var, self.arg.simplify())
            case _:
                # Atomic formulas are caught by the implementation of the
                # abstract method AtomicFormula.simplify.
                assert False, type(self)

    def subs(self, substitution: dict[χ, τ | σ]) -> Self:
        """Substitution of terms for variables.

        >>> from deesi.theories.RCF import *
        >>> a, b, x = VV.get('a', 'b', 'x')
        >>> f = Ex(x, x == a)
        >>> f.subs({x: a})
        Ex(x, a - x == 0)
        >>> f.subs({a: x})
        Ex(G0001_x, -G0001_x + x == 0)
        >>> g = Ex(x, And(_, b == 0))
        >>> g.subs({b: x})
        Ex(G0002_x, And(Ex(G0001_x, -G0001_x + G0002_x == 0), x == 0))
        """
        if Formula.is_quantified_formula(self):
            # A copy of the mutable could be avoided by keeping track of
            # the changes and undoing them at the end.
            substitution = substitution.copy()
            # (1) Remove substitution for the quantified variable. In
            # principle, this is covered by (2) below, but deleting here
            # preserves the name.
            if self.var in substitution:
                del substitution[self.var]
            # Collect all variables on the right hand sides of
            # substitutions:
            substituted_vars: set[Variable] = set()
            for term in substitution.values():
                if self.is_term(term):
                    substituted_vars.update(tuple(term.vars()))
            # (2) Make sure the quantified variable is not a key and does
            # not occur in a value of substitution:
            if self.var in substituted_vars or self.var in substitution:
                var = self.var.fresh()
                # We now know the following:
                #   (i) var is not a key,
                #  (ii) var does not occur in the values,
                # (iii) self.var is not a key.
                # We do *not* know whether self.var occurs in the values.
                substitution[self.var] = var
                # All free occurrences of self.var in self.arg will be
                # renamed to var. In case of (iv) above, substitution will
                # introduce new free occurrences of self.var, which do not
                # clash with the new quantified variable var:
                return self.op(var, self.arg.subs(substitution))  # type: ignore[return-value]
            return self.op(self.var, self.arg.subs(substitution))  # type: ignore[return-value]
        elif Formula.is_boolean_formula(self):
            return_value = self.op(*(arg.subs(substitution) for arg in self.args))
            return return_value  # type: ignore[return-value]
        else:
            # Atomic formulas are caught by the implementation of the
            # abstract method AtomicFormula.subs.
            assert False, type(self)

    def to_nnf(self, to_positive: bool = True, _not: bool = False) -> Formula[α, τ, χ, σ]:
        """Convert to Negation Normal Form.

        A Negation Normal Form (NNF) is an equivalent formula within which the
        application of :class:`Not` is restricted to atomic formulas, i.e.,
        instances of :class:`AtomicFormula`, and truth values :data:`T` and
        :data:`F`. The only other operators admitted are :class:`And`,
        :class:`Or`, :class:`Ex`, and :class:`All`.

        If the input is quanitfier-free, :meth:`to_nnf` will not introduce any
        quanitfiers.

        If `to_positive` is `True`, :class:`Not` is eliminated via replacing
        relation symbols with their complements. The result is then even a
        Positive Normal Form.

        >>> from deesi.theories.RCF import *
        >>> a, y = VV.get('a', 'y')
        >>> f = Equivalent(And(a == 0, T), Ex(y, Not(y == a)))
        >>> f.to_nnf()
        And(Or(a != 0, F, Ex(y, a - y != 0)),
            Or(All(y, a - y == 0), And(a == 0, T)))
        """
        match self:
            case All() | Ex():
                nnf_op: type[Formula[α, τ, χ, σ]] = self.dual() if _not else self.op
                nnf_arg = self.arg.to_nnf(to_positive=to_positive, _not=_not)
                return nnf_op(self.var, nnf_arg)
            case Equivalent():
                rewrite: Formula[α, τ, χ, σ] = And(Implies(*self.args),
                                                   Implies(self.rhs, self.lhs))
                return rewrite.to_nnf(to_positive=to_positive, _not=_not)
            case Implies():
                if isinstance(self.rhs, Or):
                    rewrite = Or(Not(self.lhs), *self.rhs.args)
                else:
                    rewrite = Or(Not(self.lhs), self.rhs)
                return rewrite.to_nnf(to_positive=to_positive, _not=_not)
            case And() | Or():
                nnf_op = self.dual() if _not else self.op
                nnf_args: list[Formula] = []
                for arg in self.args:
                    nnf_arg = arg.to_nnf(to_positive=to_positive, _not=_not)
                    if nnf_arg.op is nnf_op:
                        nnf_args.extend(nnf_arg.args)
                    else:
                        nnf_args.append(nnf_arg)
                return nnf_op(*nnf_args)
            case Not():
                return self.arg.to_nnf(to_positive=to_positive, _not=not _not)
            case _F() | _T():
                if _not:
                    return self.dual()() if to_positive else Not(self)
                return self
            case AtomicFormula():
                if _not:
                    if to_positive:
                        return self.to_complement()
                    return Not(self)
                return self
            case _:
                assert False, type(self)

    def traverse(self, *,
                 map_atoms: Callable[..., Formula[α, τ, χ, σ]] = lambda atom: atom,
                 sort_levels: bool = False) -> Formula[α, τ, χ, σ]:
        """Apply `tr` to all atomic formulas.

        Replaces each atomic subformula of `self` with the :class:`Formula`
        `map_atoms(self)`. If `sort_levels' is :obj:`True`, all subformulas
        built from commutative  boolean operators (:class:`.And`, :class:`.Or`,
        :class:`.Equivalent`) are sorted after the application of `map_atoms`.

        >>> from deesi.theories.RCF import *
        >>> x, y, z = VV.get('x', 'y', 'z')
        >>> f = And(x == y, y < z)
        >>> f.traverse(map_atoms=lambda atom: atom.op(atom.lhs - atom.rhs, 0))
        And(x - y == 0, y - z < 0)
        """
        # Getting rid of the "..." argument of Callable requires ParamSpecs.
        # Note: Already, before we switched to Generics, there were MyPy
        # problems with AtomicFormula in that position.
        match self:
            case All() | Ex():
                arg = self.arg.traverse(map_atoms=map_atoms, sort_levels=sort_levels)
                return self.op(self.var, arg)
            case And() | Or() | Equivalent():
                argl = list(arg.traverse(map_atoms=map_atoms, sort_levels=sort_levels)
                            for arg in self.args)
                if sort_levels:
                    argl.sort()
                return self.op(*argl)
            case Not() | Implies() | _F() | _T():
                args = (arg.traverse_atoms(map_atoms=map_atoms, sort_levels=sort_levels)
                        for arg in self.args)
                return self.op(*args)
            case AtomicFormula():
                return map_atoms(self)
            case _:
                assert False, type(self)


# The following imports are intentionally late to avoid circularity.
from .atomic import AtomicFormula, Term, Variable
from .boolean import And, BooleanFormula, Equivalent, Implies, involutive_not, Not, Or, _F, _T
from .boolean import T  # noqa, used in doctests only
from .quantified import All, Ex, QuantifiedFormula
