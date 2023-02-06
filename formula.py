"""Module for first-order formulas with equality Eq -> BinaryAtomicFormula ->
AtomicFormula. There is no language L in the sense of model theory specified.
Applications would implement their particular languages as follows:

* Relations of L are provided by subclassing AtomicFormula. More generally,
  BinaryAtomicFormula can be subclassed. More specifically, the module atomic
  provides some classes for inequalities and other relations that can be
  subclassed.

* Technically, the atomic formula classes provided here and an the module
  atomic admit *all* sympy expressions as terms. Consequently, the
  implementation of the functions of L must not provide but limit the set of
  admissible functions (which includes constants). Within the application code,
  this is a matter of self-discipline using only L-terms as arguments for the
  constructors of the relations. Explicit tests beyond assertions would take
  place only in convenience wrappers around constructors for the user
  interface; compare EX, ALL, AND, OR, EQUIV, IMPL below.
"""

import sympy
# from .tracing import trace


Variable = sympy.Symbol


class Formula:
    """A class for representing first-order formulas.

    Attributes:
    -----------
    func: a logic1 class
    args: a tuple of ``Formula``
    """

    def __and__(*args):
        """Override the bitwise and operator ``&`` for logical AND.

        Note that ``&`` delegates to the convenience wrapper AND in contrast to
        the constructor And.

        >>> Eq(0, 0) & Eq(1 + 1, 2) & Eq(1 + 1 + 1, 3)
        And(Eq(0, 0), Eq(2, 2), Eq(3, 3))
        """
        return AND(*args)

    def __invert__(a):
        """Override the bitwise invert operator ``~`` for logical NOT.

        Note that ``~`` delegates to the convenience wrapper NOT in contrast to
        the constructor Not.

        >>> ~ Eq(1,0)
        Not(Eq(1, 0))
        """
        return NOT(a)

    def __lshift__(a1, a2):
        """Override the bitwise left shift operator ``>>`` for logical IMPL.

        Note that ``>>`` delegates to the convenience wrapper IMPL in contrast
        to the constructor Implies.

        >>> from sympy.abc import x, y, z
        >>> Eq(x + z, y + z) << Eq(x, y)
        Implies(Eq(x, y), Eq(x + z, y + z))
        """
        return IMPL(a2, a1)

    def __or__(*args):
        """Override the bitwise or operator ``|`` for logical OR.

        Note that ``|`` delegates to the convenience wrapper OR in contrast to
        the constructor Or.

        >>> from sympy.abc import x, y, z
        >>> Eq(x, 0) | Eq(x, y) | Eq(x, z)
        Or(Eq(x, 0), Eq(x, y), Eq(x, z))
        """
        return OR(*args)

    def __rshift__(a1, a2):
        """Override the bitwise right shift operator ``<<`` for logical IMPL
        with reversed sides.

        Note that ``<<`` uses the convenience wrapper IMPL in contrast to the
        constructor implies.

        >>> from sympy.abc import x, y, z
        >>> Eq(x, y) >> Eq(x + z, y + z)
        Implies(Eq(x, y), Eq(x + z, y + z))
        """
        return IMPL(a1, a2)

    def __eq__(self, other):
        """Recursive equality of the formulas self and other.

        >>> e1 = Eq(1, 0)
        >>> e2 = Eq(1, 0)
        >>> e1 == e2
        True
        >>> e1 is e2
        False
        """
        return self.func == other.func and self.args == other.args

    def __init__(self, *args):
        """An initializer that always raises an exception.

        >>> Formula(Eq, 1, 0)
        Traceback (most recent call last):
        ...
        NotImplementedError: Formula is an abstract class

        This provides a hands-on implementation of an abstract class. It is
        inherited down the hierarchy. Only the the leaf classes, which
        correspond to logic operators should be instantiated.
        """
        raise NotImplementedError("Formula is an abstract class")

    def __repr__(self):
        """Representation of the Formula suitable for use as an input.

        __str__() falls back to this unless explicitly implemented in a
        subclass.
        """
        repr = self.func.__name__
        repr += "("
        if self.args:
            repr += self.args[0].__repr__()
            for a in self.args[1:]:
                repr += ", " + a.__repr__()
        repr += ")"
        return repr

    def _repr_latex_(self):
        r"""A LaTeX representation of the formula as it is used within jupyter
        notebooks

        >>> Eq(1, 0)._repr_latex_()
        '$\\displaystyle 1 = 0$'

        Subclasses have latex() methods yielding plain LaTeX without the
        surrounding $\\displaystyle ... $.
        """
        return "$\\displaystyle " + self.latex() + "$"

    def nnf(self, implicitNot=False):
        """A negation normal form that always raises an exception.

        This provides a hands-on implementation of an abstract class. It is
        inherited down the hierarchy. Only the the leaf classes, which
        correspond to logic operators should be instantiated.

        This method would get called if any leaf class missed to implement an
        nnf() method.
        """
        raise NotImplementedError(f"nnf() method missing on {self.func}")

    def simplify(self, Theta=None):
        """Identity as a default implemenation of a simplifier for formulas.

        This should be overridden in the majority of the classes that
        are finally instantiated.
        """
        return self

    def sympy(self, **kwargs):
        """Provide a sympy representation of the Formula if possible.

        Subclasses that have no match in sympy can raise NotImplementedError.

        >>> from sympy.abc import x, y
        >>> e1 = Equivalent(Eq(x, y), Eq(x + 1, y + 1))
        >>> e1
        Equivalent(Eq(x, y), Eq(x + 1, y + 1))
        >>> type(e1)
        <class 'formula.Equivalent'>
        >>> e1.sympy()
        Equivalent(Eq(x, y), Eq(x + 1, y + 1))
        >>> type(e1.sympy())
        Equivalent

        >>> e2 = Equivalent(Eq(x, y), Eq(y, x))
        >>> e2
        Equivalent(Eq(x, y), Eq(y, x))
        >>> e2.sympy()
        True

        >>> e3 = T
        >>> e3.sympy()
        Traceback (most recent call last):
        ...
        NotImplementedError: no sympy representation of <class 'formula._T'> available

        >>> e4 = All(x, Ex(y, Eq(x, y)))
        >>> e4.sympy()
        Traceback (most recent call last):
        ...
        NotImplementedError
        """
        return self._sympy_func(*(a.sympy(**kwargs) for a in self.args))


class QuantifiedFormula(Formula):

    _latex_precedence = 99
    _latex_symbol_spacing = "\\,"

    is_atomic = False
    is_boolean = False
    is_quantified = True

    @property
    def variable(self):
        """The variable of the quantifier.

        >>> from sympy.abc import x, y
        >>> e1 = All(x, Ex(y, Eq(x, y)))
        >>> e1.variable
        x
        """
        return self.args[0]

    @property
    def matrix(self):
        """The subformula in the scope of the QuantifiedFormula.

        >>> from sympy.abc import x, y
        >>> e1 = All(x, Ex(y, Eq(x, y)))
        >>> e1.matrix
        Ex(y, Eq(x, y))
        """
        return self.args[1]

    def latex(self):
        r"""A LaTeX representation of the QuantifiedFormula.

        >>> from sympy.abc import x, y
        >>> All(x, Ex(y, Implies(Not(Eq(x, 0)), Eq(x * y, 1)))).latex()
        '\\forall x \\, \\exists y \\, (\\neg \\, (x = 0) \\, \\longrightarrow \\, x y = 1)'
        """
        def latex_in_parens(inner):
            inner_Latex = inner.latex()
            if not inner.is_quantified and inner.func is not Not:
                inner_Latex = "(" + inner_Latex + ")"
            return inner_Latex

        self_latex = self._latex_symbol
        self_latex += " " + str(self.args[0])
        self_latex += " " + self._latex_symbol_spacing
        self_latex += " " + latex_in_parens(self.args[1])
        return self_latex

    def nnf(self, implicitNot: bool = False):
        func_nnf = self.func.dualize(conditional=implicitNot)
        matrix_nnf = self.matrix.nnf(implicitNot=implicitNot)
        return func_nnf(self.variable, matrix_nnf)

    def simplify(self, Theta=None):
        """Simplification.

        >>> from sympy.abc import x, y
        >>> All(x, Ex(y, Eq(x, y))).simplify()
        All(x, Ex(y, Eq(x, y)))
        """
        return self.func(self.variable, self.matrix.simplify())

    def sympy(self, *args, **kwargs):
        print(f"sympy representation of {type(self)} is not available.")
        raise NotImplementedError


class Ex(QuantifiedFormula):
    """
    >>> from sympy.abc import x
    >>> Ex(x, Eq(x, 1))
    Ex(x, Eq(x, 1))
    """
    _latex_symbol = "\\exists"

    @staticmethod
    def dualize(conditional: bool = True):
        if conditional:
            return All
        return Ex

    def __init__(self, variable, matrix):
        self.func = Ex
        self.args = (variable, matrix)


def EX(variable, matrix):
    """A convenience wrapper for the Ex Formula constructor, which does type
    checking.

    This is intended for inteactive use.

    >>> from sympy.abc import x
    >>> EX(x, Eq(x, x))
    Ex(x, Eq(x, x))

    For efficiency reasons, the constructors of subclasses of Formula do not
    check argument types. Trouble following later on can be hard to diagnose:
    >>> f = Ex("x", "y")
    >>> f
    Ex('x', 'y')
    >>> f.simplify()
    Traceback (most recent call last):
    ...
    AttributeError: 'str' object has no attribute 'simplify'

    EX checks and raises an exception immediately:
    >>> EX("x", Eq(x, x))
    Traceback (most recent call last):
    ...
    TypeError: x is not a Variable
    """
    if not isinstance(variable, Variable):
        raise TypeError(f"{variable} is not a Variable")
    if not isinstance(matrix, Formula):
        raise TypeError(f"{matrix} is not a Formula")
    return Ex(variable, matrix)


class All(QuantifiedFormula):
    """
    >>> from sympy.abc import x, y
    >>> All(x, All(y, Eq((x + y)**2 + 1, x**2 + 2*x*y + y**2)))
    All(x, All(y, Eq((x + y)**2 + 1, x**2 + 2*x*y + y**2)))
    """
    _latex_symbol = "\\forall"

    @staticmethod
    def dualize(conditional: bool = True):
        if conditional:
            return Ex
        return All

    def __init__(self, variable, matrix):
        self.func = All
        self.args = (variable, matrix)


def ALL(variable, matrix):
    """A convenience wrapper for the All Formula constructor, which does type
    checking.

    This is intended for inteactive use.

    >>> from sympy.abc import x
    >>> ALL(x, Eq(x, x))
    All(x, Eq(x, x))

    For efficiency reasons, the constructors of subclasses of Formula do not
    check argument types. Trouble following later on can be hard to diagnose:
    >>> f = All("x", "y")
    >>> f
    All('x', 'y')
    >>> f.simplify()
    Traceback (most recent call last):
    ...
    AttributeError: 'str' object has no attribute 'simplify'

    ALL checks and raises an exception immediately:
    >>> ALL("x", Eq(x, x))
    Traceback (most recent call last):
    ...
    TypeError: x is not a Variable
    """
    if not isinstance(variable, Variable):
        raise TypeError(f"{variable} is not a Variable")
    if not isinstance(matrix, Formula):
        raise TypeError(f"{matrix} is not a Formula")
    return All(variable, matrix)


class BooleanFormula(Formula):
    """Boolean Formulas have a Boolean operator at the top level.

    An operator of a Formula is either a quantifier Ex, All or a Boolean
    operator And, Or, Not, Implies, Equivaelent, T, F. Note that members of
    BooleanFormula start, in the sense of prefix notation, with a Boolean
    operator but may have quantified subformulas deeper in the expression tree.
    """

    _latex_symbol_spacing = "\\,"

    is_atomic = False
    is_boolean = True
    is_quantified = False

    def latex(self):
        def not_latex_in_parens(outer, inner):
            inner_latex = inner.latex()
            if inner.func is not outer.func and not inner.is_quantified:
                inner_latex = "(" + inner_latex + ")"
            return inner_latex

        def infix_latex_in_parens(outer, inner):
            inner_latex = inner.latex()
            if outer._latex_precedence >= inner._latex_precedence:
                inner_latex = "(" + inner_latex + ")"
            return inner_latex

        if self._latex_style == "constant":
            return self._latex_symbol
        if self._latex_style == "not":
            self_latex = self._latex_symbol
            self_latex += " " + self._latex_symbol_spacing
            return self_latex + " " + not_latex_in_parens(self, self.arg)
        if self._latex_style == "infix":
            self_latex = infix_latex_in_parens(self, self.args[0])
            for a in self.args[1:]:
                self_latex += " " + self._latex_symbol_spacing
                self_latex += " " + self._latex_symbol
                self_latex += " " + self._latex_symbol_spacing
                self_latex += " " + infix_latex_in_parens(self, a)
            return self_latex
        assert False


class Equivalent(BooleanFormula):

    _latex_style = "infix"
    _latex_symbol = "\\longleftrightarrow"
    _latex_precedence = 10
    _sympy_func = sympy.Equivalent

    @property
    def lhs(self):
        """The left-hand side of the Equivalence."""
        return self.args[0]

    @property
    def rhs(self):
        """The right-hand side of the Equivalence."""
        return self.args[1]

    def __init__(self, lhs, rhs):
        self.func = Equivalent
        self.args = (lhs, rhs)

    def nnf(self, implicitNot=False):
        tmp = And(Implies(self.lhs, self.rhs), Implies(self.rhs, self.lhs))
        return tmp.nnf(implicitNot=implicitNot)

    def simplify(self, Theta=None):
        """Recursively simplify the Equivalence.

        >>> from sympy.abc import x, y
        >>> e1 = Equivalent(Not(Eq(x, y)), F)
        >>> e1.simplify()
        Eq(x, y)
        """
        lhs = self.lhs.simplify(Theta=Theta)
        rhs = self.rhs.simplify(Theta=Theta)
        if lhs is T:
            return rhs
        if rhs is T:
            return lhs
        if lhs is F:
            if rhs.func is Not:
                return rhs.arg
            return Not(rhs)
        if rhs is F:
            if lhs.func is Not:
                return lhs.arg
            return Not(lhs)
        if lhs == rhs:
            return True
        return Equivalent(lhs, rhs)


def EQUIV(lhs, rhs):
    if not isinstance(lhs, Formula):
        raise TypeError(f"{lhs} is not a Formula")
    if not isinstance(rhs, Formula):
        raise TypeError(f"{rhs} is not a Formula")
    return Equivalent(lhs, rhs)


class Implies(BooleanFormula):

    _latex_style = "infix"
    _latex_symbol = "\\longrightarrow"
    _latex_precedence = 10

    _sympy_func = sympy.Implies

    @property
    def lhs(self):
        """The left-hand side of the Implies."""
        return self.args[0]

    @property
    def rhs(self):
        """The right-hand side of the Implies."""
        return self.args[1]

    def __init__(self, lhs, rhs):
        self.func = Implies
        self.args = (lhs, rhs)

    def nnf(self, implicitNot=False):
        return Or(Not(self.lhs), self.rhs).nnf(implicitNot=implicitNot)

    def simplify(self, Theta=None):
        if self.rhs is T:
            return self.lhs
        lhs_simplify = self.lhs.simplify(Theta=Theta)
        if lhs_simplify is F:
            return T
        rhs_simplify = self.rhs.simplify(Theta=Theta)
        if rhs_simplify is T:
            return T
        if lhs_simplify is T:
            return rhs_simplify
        if rhs_simplify is F:
            return involutive_not(lhs_simplify)
        assert not isinstance(lhs_simplify, TruthValue)
        assert not isinstance(rhs_simplify, TruthValue)
        if lhs_simplify == rhs_simplify:
            return T
        return Implies(lhs_simplify, rhs_simplify)


def IMPL(lhs, rhs):
    if not isinstance(lhs, Formula):
        raise TypeError(f"{lhs} is not a Formula")
    if not isinstance(rhs, Formula):
        raise TypeError(f"{rhs} is not a Formula")
    return Implies(lhs, rhs)


class AndOr(BooleanFormula):
    _latex_style = "infix"
    _latex_precedence = 50

    def nnf(self, implicitNot=False):
        """Negation normal form.
        """
        func_nnf = self.func.dualize(conditional=implicitNot)
        args_nnf = (arg.nnf(implicitNot=implicitNot) for arg in self.args)
        return func_nnf(*args_nnf)

    def simplify(self, Theta=None):
        """Simplification.

        >>> from sympy.abc import x, y, z
        >>> And(Eq(x, y), T, Eq(x, y), And(Eq(x, z), Eq(x, x + z))).simplify()
        And(Eq(x, y), Eq(x, z), Eq(x, x + z))
        >>> Or(Eq(x, 0), Or(Eq(x, 1), Eq(x, 2)), And(Eq(x, y), Eq(x, z))).simplify()
        Or(Eq(x, 0), Eq(x, 1), Eq(x, 2), And(Eq(x, y), Eq(x, z)))
        """
        gAnd = And.dualize(conditional=self.func is Or)
        gT = _T.dualize(conditional=self.func is Or)()
        gF = _F.dualize(conditional=self.func is Or)()
        # gAnd is an AndOr func, gT and gF are complete TruthValue singletons
        simplified_args = []
        for arg in self.args:
            arg_simplify = arg.simplify()
            if arg_simplify is gF:
                return gF
            if arg_simplify is gT:
                continue
            if arg_simplify in simplified_args:
                continue
            if arg_simplify.func is gAnd:
                simplified_args.extend(arg_simplify.args)
            else:
                simplified_args.append(arg_simplify)
        if not simplified_args:
            return gT
        return gAnd(*simplified_args)


class And(AndOr):
    """Constructor for conjunctions of Formulas.

    >>> from sympy.abc import x, y, z
    >>> And()
    T
    >>> And(Eq(0, 0))
    Eq(0, 0)
    >>> And(Eq(x, 0), Eq(x, y), Eq(y, z))
    And(Eq(x, 0), Eq(x, y), Eq(y, z))
    """
    _latex_symbol = "\\wedge"
    _sympy_func = sympy.And

    @staticmethod
    def dualize(conditional: bool = True):
        if conditional:
            return Or
        return And

    def __new__(cls, *args):
        if not args:
            return T
        if len(args) == 1:
            return args[0]
        return super().__new__(cls)

    def __init__(self, *args):
        self.func = And
        self.args = args


def AND(*args):
    for arg in args:
        if not isinstance(arg, Formula):
            raise TypeError(f"{arg} is not a Formula")
    args_flat = []
    for arg in args:
        if arg.func is And:
            args_flat.extend(list(arg.args))
        else:
            args_flat.append(arg)
    return And(*args_flat)


class Or(AndOr):
    """Constructor for disjunctions of Formulas.

    >>> Or()
    F
    >>> Or(Eq(1, 0))
    Eq(1, 0)
    >>> Or(Eq(1, 0), Eq(2, 0), Eq(3, 0))
    Or(Eq(1, 0), Eq(2, 0), Eq(3, 0))
    """
    _latex_symbol = "\\vee"
    _sympy_func = sympy.Or

    @staticmethod
    def dualize(conditional: bool = True):
        if conditional:
            return And
        return Or

    def __new__(cls, *args):
        if not args:
            return F
        if len(args) == 1:
            return args[0]
        return super().__new__(cls)

    def __init__(self, *args):
        self.func = Or
        self.args = args


def OR(*args):
    for arg in args:
        if not isinstance(arg, Formula):
            raise TypeError(f"{arg} is not a Formula")
    args_flat = []
    for arg in args:
        if arg.func is Or:
            args_flat.extend(list(arg.args))
        else:
            args_flat.append(arg)
    return Or(*args_flat)


class Not(BooleanFormula):

    _latex_style = "not"
    _latex_symbol = "\\neg"
    _latex_precedence = 99

    _sympy_func = sympy.Not

    @property
    def arg(self):
        """The one argument of the Not."""
        return self.args[0]

    def __init__(self, arg):
        self.func = Not
        self.args = (arg, )

    def nnf(self, implicitNot=False):
        """Negation normal form.

        >>> from sympy.abc import x, y, z
        >>> f = All(x, EX(y, And(Eq(x, y), T, Eq(x, y), And(Eq(x, z), Eq(y, x)))))
        >>> Not(f).nnf()
        Ex(x, All(y, Or(Not(Eq(x, y)), F, Not(Eq(x, y)), Or(Not(Eq(x, z)), Not(Eq(y, x))))))
        """
        return self.arg.nnf(implicitNot=not implicitNot)

    def simplify(self, Theta=None):
        """Simplification.

        >>> from sympy.abc import x, y, z
        >>> f = All(x, EX(y, And(Eq(x, y), T, Eq(x, y), And(Eq(x, z), Eq(y, x)))))
        >>> Not(f).simplify()
        Not(All(x, Ex(y, And(Eq(x, y), Eq(x, z), Eq(y, x)))))
        """
        arg_simplify = self.arg.simplify(Theta=Theta)
        if arg_simplify is T:
            return F
        if arg_simplify is F:
            return T
        return involutive_not(arg_simplify)


def NOT(arg):
    if not isinstance(arg, Formula):
        raise TypeError(f"{arg} is not a Formula")
    return Not(arg)


def involutive_not(arg: Formula):
    """Construct a formula equivalent Not(arg) using the involutive law if
    applicable.

    >>> involutive_not(Eq(0, 0))
    Not(Eq(0, 0))
    >>> involutive_not(Not(Eq(1, 0)))
    Eq(1, 0)
    >>> involutive_not(T)
    Not(T)
    """
    if arg.func is Not:
        return arg.arg
    return Not(arg)


class TruthValue(BooleanFormula):

    _latex_style = "constant"
    _latex_precedence = 99

    def nnf(self, implicitNot=False):
        return self.func.dualize(conditional=implicitNot)()

    def sympy(self):
        raise NotImplementedError(f"no sympy representation of {self.func} available")


class _T(TruthValue):
    """The constant Formula that is always true.

    This is a quite basic implementation of a singleton class. It does not
    support subclassing. We do not use a module because we need _T to be a
    subclass itself.
    """
    _latex_symbol = "\\top"

    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

    @staticmethod
    def dualize(conditional: bool = True):
        if conditional:
            return _F
        return _T

    def __init__(self):
        self.func = _T
        self.args = ()

    def __repr__(self):
        return "T"


T = _T()


class _F(TruthValue):
    """The constant Formula that is always false.

    This is a quite basic implementation of a singleton class. It does not
    support subclassing. We do not use a module because we need _F to be a
    subclass itself.
    """
    _latex_symbol = "\\bot"

    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

    @staticmethod
    def dualize(conditional: bool = True):
        if conditional:
            return _T
        return _F

    def __init__(self):
        self.func = _F
        self.args = ()

    def __repr__(self):
        return "F"


F = _F()


class AtomicFormula(BooleanFormula):

    _latex_symbol_spacing = ""
    _latex_precedence = 99

    is_atomic = True
    is_boolean = False
    is_quantified = False

    def nnf(self, implicitNot=False):
        if implicitNot:
            return Not(self)
        return self

    # Override Formula.sympy() to prevent recursion into terms
    def sympy(self, **kwargs):
        return self._sympy_func(*self.args, **kwargs)


class BinaryAtomicFormula(AtomicFormula):

    @property
    def lhs(self):
        """The left-hand side of the BinaryAtomicFormula."""
        return self.args[0]

    @property
    def rhs(self):
        """The right-hand side of the BinaryAtomicFormula."""
        return self.args[1]

    # Override BooleanFormula.latex() to prevent recursion into terms
    def latex(self):
        self_latex = sympy.latex(self.lhs)
        self_latex += " " + self._latex_symbol_spacing
        self_latex += self._latex_symbol
        self_latex += " " + self._latex_symbol_spacing
        self_latex += sympy.latex(self.rhs)
        return self_latex


class Eq(BinaryAtomicFormula):
    """
    >>> from sympy.abc import x
    >>> Eq(x, x)
    Eq(x, x)
    """
    _latex_symbol = "="
    _sympy_func = sympy.Eq

    def __init__(self, lhs, rhs):
        self.func = Eq
        self.args = (lhs, rhs)