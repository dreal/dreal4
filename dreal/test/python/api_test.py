# -*- coding: utf-8 -*-
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

from dreal import *

import math
import unittest

x = Variable("x")
y = Variable("y")
z = Variable("z")
p = Variable("p")
x0 = Variable("x0")
x1 = Variable("x1")
x2 = Variable("x2")

f_sat = And(0 <= x, x <= 10, 0 <= y, y <= 10, 0 <= z, z <= 10,
            sin(x) + cos(y) == z)

f_unsat = And(3 <= x, x <= 4, 4 <= y, y <= 5, 5 <= z, z <= 6,
              sin(x) + cos(y) == z)

objective = 2 * x * x + 6 * x + 5
constraint = And(-10 <= x, x <= 10)


class ApiTest(unittest.TestCase):
    def test_delta_sat(self):
        result = CheckSatisfiability(f_sat, 0.001)
        self.assertEqual(type(result), Box)

        b = Box([x, y, z])
        result = CheckSatisfiability(f_sat, 0.001, b)
        self.assertEqual(result, True)
        self.assertTrue(b[x].diam() < 0.1)
        self.assertTrue(b[y].diam() < 0.1)
        self.assertTrue(b[z].diam() < 0.1)

    def test_unsat(self):
        result = CheckSatisfiability(f_unsat, 0.001)
        self.assertEqual(result, None)

        b = Box([x, y, z])
        b_copy = Box([x, y, z])
        result = CheckSatisfiability(f_unsat, 0.001, b)
        self.assertEqual(result, False)
        self.assertEqual(b, b_copy)  # Unchanged

    def test_minimize1(self):
        result = Minimize(objective, constraint, 0.00001)
        self.assertTrue(result)
        self.assertAlmostEqual(result[x].mid(), -1.5, places=2)

    def test_minimize2(self):
        b = Box([x])
        result = Minimize(objective, constraint, 0.00001, b)
        self.assertTrue(result)
        self.assertAlmostEqual(b[x].mid(), -1.5, places=2)

    def test_minimize3(self):
        result = Minimize(x, And(0 <= x, x <= 1, 0 <= p, p <= 1, p <= x),
                          0.00001)
        self.assertTrue(result)
        self.assertAlmostEqual(result[x].mid(), 0, places=2)
        self.assertAlmostEqual(result[p].mid(), 0, places=2)

    def test_lorentz_cone(self):
        config = Config()
        config.use_local_optimization = True
        config.precision = 0.0001
        result = Minimize(
            x2,
            And(-5 <= x0, x0 <= 5, -5 <= x1, x1 <= 5, 0 <= x2, x2 <= 5, 1 >=
                (x0 - 1)**2 + (x1 - 1)**2, x2**2 >= x0**2 + x1**2), config)
        self.assertTrue(result)
        self.assertAlmostEqual(result[x2].mid(), 0.414212, places=3)

    def test_minimize_via_forall(self):
        # To minimize f(X) s.t. φ(x), this test encodes
        # the problem into a first-order logic formula.
        #
        #    ∃X. φ(X) ∧ [∀Y φ(Y) ⇒ (f(X) ≤ f(Y))]
        #
        # Here we use f(x) = sin(x)cos(x)
        #             φ(X) = (0 ≤ x) ∧ (x ≤ π)
        def f(x):
            return sin(x) * cos(x)

        def phi(x):
            return And(0 <= x, x <= math.pi)

        problem = And(phi(x), forall([y], And(Implies(phi(y), f(x) <= f(y)))))
        result = CheckSatisfiability(problem, 0.01)
        self.assertTrue(result)
        self.assertAlmostEqual(result[x].mid(), math.pi * 3 / 4, places=3)


if __name__ == '__main__':
    unittest.main()
