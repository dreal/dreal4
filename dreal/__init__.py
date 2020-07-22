#!/usr/bin/env python
# -*- coding: utf-8 -*-
from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

from dreal._dreal_py import *
from functools import reduce

# Explicitly import private symbols
from dreal._dreal_py import __logical_and, __logical_or


def logical_and(*formulas):
    assert len(formulas) >= 1, "Must supply at least one operand"
    return reduce(__logical_and, formulas)


def logical_or(*formulas):
    assert len(formulas) >= 1, "Must supply at least one operand"
    return reduce(__logical_or, formulas)


__version__ = "4.20.07.1".replace(".0", ".")

# Add aliases
And = logical_and
Or = logical_or
Not = logical_not
Iff = logical_iff
Implies = logical_imply
