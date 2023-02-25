from __future__ import annotations

from itertools import combinations
import logging

import sympy

from logic1 import atomlib
from logic1 import abc
from logic1.firstorder.boolean import And, Or
from logic1.firstorder.formula import Formula


logging.basicConfig(
    format='%(levelname)s[%(relativeCreated)0.0f ms]: %(message)s',
    level=logging.CRITICAL)


def show_progress(flag: bool = True) -> None:
    if flag:
        logging.getLogger().setLevel(logging.INFO)
    else:
        logging.getLogger().setLevel(logging.CRITICAL)


Term = sympy.Symbol
Variable = sympy.Symbol


class TermMixin():

    @staticmethod
    def term_type() -> type[Term]:
        return Term

    @staticmethod
    def variable_type() -> type[Variable]:
        return Variable


class Eq(TermMixin, atomlib.sympy.Eq):
    """Equations with only variables as terms.

    This implements that fact that the language of sets has no functions and,
    in particular, no constants.

    >>> from sympy.abc import x, y
    >>> EQ(x, y)
    Eq(x, y)

    >>> EQ(x, 0)
    Traceback (most recent call last):
    ...
    TypeError: 0 is not a Term

    >>> EQ(x + x, y)
    Traceback (most recent call last):
    ...
    TypeError: 2*x is not a Term
    """
    @staticmethod
    def rel_complement(conditional: bool = True) -> type[Eq] | type[Ne]:
        if conditional:
            return Ne
        return Eq

    @staticmethod
    def rel_converse(conditional: bool = True) -> type[Eq] | type[Ne]:
        return Eq

    @staticmethod
    def rel_dual(conditional: bool = True) -> type[Eq] | type[Ne]:
        if conditional:
            return Ne
        return Eq


EQ = Eq.interactive_new


class Ne(TermMixin, atomlib.sympy.Ne):
    """Inequations with only variables as terms.

    This implements that fact that the language of sets has no functions and,
    in particular, no constants.

    >>> from sympy.abc import x, y
    >>> NE(y, x)
    Ne(y, x)

    >>> NE(x, y + 1)
    Traceback (most recent call last):
    ...
    TypeError: y + 1 is not a Term
    """
    @staticmethod
    def rel_complement(conditional: bool = True) -> type[Eq] | type[Ne]:
        if conditional:
            return Eq
        return Ne

    @staticmethod
    def rel_converse(conditional: bool = True) -> type[Eq] | type[Ne]:
        return Ne

    @staticmethod
    def rel_dual(conditional: bool = True) -> type[Eq] | type[Ne]:
        if conditional:
            return Eq
        return Ne


NE = Ne.interactive_new


oo = atomlib.sympy.oo


class _C(atomlib.sympy._C):
    @staticmethod
    def rel_complement(conditional: bool = True) -> type[_C] | type[_C_bar]:
        if conditional:
            return _C_bar
        return _C


C = _C.interactive_new


class _C_bar(atomlib.sympy._C_bar):
    @staticmethod
    def rel_complement(conditional: bool = True) -> type[_C] | type[_C_bar]:
        if conditional:
            return _C
        return _C_bar


C_bar = _C_bar.interactive_new


class QuantifierElimination(abc.qe.QuantifierElimination):
    """Quantifier elimination for the theory of Sets.

    >>> from logic1 import *
    >>> from sympy.abc import a, u, v, w, x, y, z
    >>> f = ALL(u, EX(w, ALL(x, EX(y, EX(v, \
            (EQ(u, v) | NE(v, w)) & ~ EQUIV(EQ(u, x), NE(u, w)) & EQ(y, a))))))
    >>> qe(f)
    C_bar(2)

    >>> g = EX(x, EX(y, EX(z, NE(x, y) & NE(x, z) & NE(y, z) \
            & ALL(u, EQ(u, x) | EQ(u, y) | EQ(u, z)))))
    >>> qe(g)
    And(C(2), C(3), C_bar(4))

    >>> h = EX(w, EX(x, NE(w, x))) >> EX(w, EX(x, EX(y, EX(z, \
            NE(w, x) & NE(w, y) & NE(w, z) & NE(x, y) & NE(x, z) & NE(y, z)))))
    >>> qe(h)
    Or(And(C(2), C(3), C(4)), C_bar(2))
    """

    def __call__(self, f):
        return self.qe(f)

    def qe1p(self, v: Variable, f: Formula) -> Formula:
        def eta(Z: set, k: int) -> Formula:
            args = []
            for k_choice in combinations(Z, k):
                args1 = []
                for z in Z:
                    args_inner = []
                    for chosen_z in k_choice:
                        args_inner.append(Eq(z, chosen_z))
                    args1.append(Or(*args_inner))
                f1 = And(*args1)
                args2 = []
                for i in range(k):
                    for j in range(i + 1, k):
                        args2.append(Ne(k_choice[i], k_choice[j]))
                f2 = And(*args2)
                args.append(And(f1, f2))
            return Or(*args)

        logging.info(f'{self.qe1p.__qualname__}: eliminating Ex {v} ({f})')
        eqs, nes = self._split_by_relation(f)
        if eqs:
            solution = eqs[0].rhs if eqs[0].rhs != v else eqs[0].lhs
            return f.subs({v: solution})
        Z = And(*nes).get_vars().free - {v}
        m = len(Z)
        phi_prime = Or(*(And(eta(Z, k), C(k + 1)) for k in range(1, m + 1)))
        logging.info(f'{self.qe1p.__qualname__}: result is {phi_prime}')
        return phi_prime

    @staticmethod
    def is_valid_atom(f: Formula) -> bool:
        return isinstance(f, (Eq, Ne, _C, _C_bar))

    @staticmethod
    def _split_by_relation(f) -> tuple[list[type[Eq]], list[type[Ne]]]:
        eqs = []
        nes = []
        args = f.args if f.func is And else (f,)
        for atom in args:
            if atom.func is Eq:
                eqs.append(atom)
            else:
                assert atom.func is Ne, f'bad atom {atom} - {atom.func}'
                nes.append(atom)
        return eqs, nes


qe = quantifier_elimination = QuantifierElimination()
