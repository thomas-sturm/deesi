__version__ = 0.1

___author___ = 'Nicolas Faroß, Thomas Sturm'
___contact___ = 'faross@math.uni-sb.de, tsturm@me.com'
___copyright__ = 'Copyright 2023, N. Faroß, T. Sturm, Germany'
___license__ = 'GPL-2.0-or-later'
___status__ = 'Prototype'

from . import firstorder

from .firstorder import (Formula, AtomicFormula, Term, Variable,  # noqa
                         BooleanFormula, Equivalent, Implies, And, Or, Not,
                         T, F, QuantifiedFormula, Ex, All)

from . import RCF
from .RCF import *  # noqa

__all__ = firstorder.__all__ + RCF.__all__
