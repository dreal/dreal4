# -*- coding: utf-8 -*-
from dreal.symbolic import Variable, logical_and, sin, cos
from dreal.symbolic import logical_imply, forall
from dreal.api import CheckSatisfiability, Minimize
from dreal.util import Box
import math
import unittest

x = Variable("x")
y = Variable("y")
z = Variable("z")

f_sat = logical_and(0 <= x, x <= 10,
                    0 <= y, y <= 10,
                    0 <= z, z <= 10,
                    sin(x) + cos(y) == z)

f_unsat = logical_and(3 <= x, x <= 4,
                      4 <= y, y <= 5,
                      5 <= z, z <= 6,
                      sin(x) + cos(y) == z)

objective = 2 * x * x + 6 * x + 5
constraint = logical_and(-10 <= x, x <= 10)


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
            return logical_and(0 <= x, x <= math.pi)

        problem = logical_and(phi(x),
                              forall([y],
                                     logical_and(logical_imply(phi(y),
                                                               f(x) <= f(y)))))
        result = CheckSatisfiability(problem, 0.01)
        self.assertTrue(result)
        self.assertAlmostEqual(result[x].mid(), math.pi * 3 / 4, places=3)


if __name__ == '__main__':
    unittest.main()
