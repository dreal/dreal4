# -*- coding: utf-8 -*-
from dreal.symbolic import Variable, logical_and, sin, cos, tan, exp, log, sqrt
from dreal.symbolic import logical_imply, forall
from dreal.api import CheckSatisfiability, Minimize
from dreal.util import Box
from dreal.solver import Config
import math
import unittest

x = Variable("x")
y = Variable("y")
z = Variable("z")

config = Config()
config.precision = 0.001


class ApiTest(unittest.TestCase):
    def test_ackley(self):
        domain = logical_and(-5 <= x, x <= 5,
                             -5 <= y, y <= 5)
        objective = (-20 * exp(-0.2 * sqrt(0.5 * (x ** 2 + y ** 2)))
                     - exp(0.5 * (cos(2 * 3.141592 * x)
                                  + cos(2 * 3.141592 * y)))
                     + 2.71828182846 + 20)
        result = Minimize(objective, domain, config)
        print(type(result))
        print(result)


if __name__ == '__main__':
    unittest.main()
