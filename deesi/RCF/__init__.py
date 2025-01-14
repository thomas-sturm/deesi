"""A theory package for Real Closed Fields.
"""

from .atomic import cache_clear, cache_info, Eq, Ne, Ge, Le, Gt, Lt, Term, Variable, VV
from . import redlog
from .simplify import is_valid, simplify

__all__ = [
    'Eq', 'Ne', 'Ge', 'Le', 'Gt', 'Lt', 'Term', 'Variable', 'VV',

    'redlog',

    'is_valid', 'simplify',

    'cache_clear', 'cache_info'
]
