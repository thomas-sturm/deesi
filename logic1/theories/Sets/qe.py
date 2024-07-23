import logging

from itertools import combinations

from ... import depricated
from ...firstorder import And, Or
from .atomic import C, Eq, Ne, Variable
from .bnf import dnf as _dnf
from .simplify import simplify as _simplify
from .typing import Formula

from ...support.tracing import trace  # noqa


class Pool(depricated.qe.PoolOnePrimitive):

    def dnf(self, f: Formula) -> Formula:
        return _dnf(f)


class QuantifierElimination(depricated.qe.QuantifierElimination):
    """Quantifier elimination for the theory of Sets.

    >>> from logic1.firstorder import *
    >>> from logic1.theories.Sets import *
    >>> a, u, v, w, x, y, z = VV.get('a', 'u', 'v', 'w', 'x', 'y', 'z')
    >>> f = All(u, Ex(w, All(x, Ex([y, v], And(Or(u == v, v != w),
    ...                                        ~ Equivalent(u == x, u != w),
    ...                                        y == a)))))
    >>> qe(f)
    C_(2)
    >>> g = Ex([x, y, z],
    ...        And(x != y, x != z, y != z, All(u, Or(u == x, u == y, u == z))))
    >>> qe(g)
    And(C(3), C_(4))
    >>> h = Implies(Ex([w, x], w != x),
    ...             Ex([w, x, y, z],
    ...                And(w != x, w != y, w != z, x != y, x != z, y != z)))
    >>> qe(h)
    Or(C_(2), C(4))
    """

    def __call__(self, f, sism: bool = True, show_progress: bool = False) -> Formula:
        if show_progress:
            save_level = logging.getLogger().getEffectiveLevel()
            logging.getLogger().setLevel(logging.INFO)
        self.sism = sism
        result = self.qe(f)
        if show_progress:
            logging.getLogger().setLevel(save_level)
        return result

    def select_and_pop(self, vars_: list, f: Formula) -> Variable:
        # revise: use a counter
        d = {v: 0 for v in vars_}
        args = f.args if f.op is And else (f,)
        for atom in args:
            for v in set(atom.fvars()):
                if v in vars_:
                    d[v] += 1
        vals = list(d.values())
        keys = list(d.keys())
        v = keys[vals.index(min(vals))]
        vars_.remove(v)
        # print(d, v)
        return v

    def _Pool(self, vars_: list[Variable], f: Formula) -> Pool:
        return Pool(vars_, f)

    def qe1(self, v: Variable, f: Formula) -> Formula:
        def eta(Z: set, k: int) -> Formula:
            args = []
            for k_choice in combinations(Z, k):
                args1: list[Formula] = []
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

        logging.info(f'{self.qe1.__qualname__}: eliminating Ex {v} ({f})')
        eqs, nes = self._split_by_relation(f)
        if eqs:
            solution = eqs[0].rhs if eqs[0].rhs != v else eqs[0].lhs
            return f.subs({v: solution})
        Z = set(And(*nes).fvars()) - {v}
        m = len(Z)
        args = (And(eta(Z, k), C(k + 1)) for k in range(1, m + 1))
        phi_prime: Formula = Or(*args)
        logging.info(f'{self.qe1.__qualname__}: result is {phi_prime}')
        return phi_prime

    def simplify(self, f: Formula) -> Formula:
        return _simplify(f) if self.sism else f.simplify()

    @staticmethod
    def _split_by_relation(f) -> tuple[list[Eq], list[Ne]]:
        eqs = []
        nes = []
        args = f.args if f.op is And else (f,)
        for atom in args:
            if atom.op is Eq:
                eqs.append(atom)
            else:
                assert atom.op is Ne, f'bad atom {atom} - {atom.op}'
                nes.append(atom)
        return eqs, nes


qe = quantifier_elimination = QuantifierElimination()
