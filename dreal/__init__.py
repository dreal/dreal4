# -*- coding: utf-8 -*-
#
#
#  Copyright 2017 Toyota Research Institute
#
#  Licensed under the Apache License, Version 2.0 (the "License");
#  you may not use this file except in compliance with the License.
#  You may obtain a copy of the License at
#
#    http://www.apache.org/licenses/LICENSE-2.0
#
#  Unless required by applicable law or agreed to in writing, software
#  distributed under the License is distributed on an "AS IS" BASIS,
#  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#  See the License for the specific language governing permissions and
#  limitations under the License.
#
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


__version__ = "4.21.06.2".replace(".0", ".")

# Add aliases
And = logical_and
Or = logical_or
Not = logical_not
Iff = logical_iff
Implies = logical_imply
