from dreal.symbolic import Variable, logical_and, sin, cos
from dreal.api import CheckSatisfiability, Minimize
from dreal.util import Box
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

    def test_minimize(self):
        result = Minimize(objective, constraint, 0.01)
        self.assertTrue(result)
        self.assertAlmostEqual(result[x].mid(), -1.5, places=2)

        b = Box([x])
        result = Minimize(objective, constraint, 0.01, b)
        self.assertTrue(result)
        self.assertAlmostEqual(b[x].mid(), -1.5, places=2)


if __name__ == '__main__':
    unittest.main()
