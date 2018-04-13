# -*- coding: utf-8 -*-
# ----------------------------------------------------------------------
# Optimization Benchmark in the following paper
# ----------------------------------------------------------------------
# Delta-Decision Procedures for Exists-Forall Problems over the Reals
# Soonho Kong, Armando Solar-Lezama, and Sicun Gao
# In CAV (International Conference on Computer Aided Verification) 2018
# ----------------------------------------------------------------------
from dreal.symbolic import (Formula, Variable, Expression, logical_imply,
                            logical_and, abs, atan, atan2, sin, cos, tan, exp,
                            log, sqrt)
from dreal.api import CheckSatisfiability, Minimize
from dreal.util import Box
from dreal.solver import Config
from functools import reduce
import math
import time
import unittest

x = Variable("x")
x1 = Variable("x1")
x2 = Variable("x2")
y = Variable("y")
z = Variable("z")


def make_default_config():
    config = Config()
    config.precision = 0.001
    return config


def make_domain(tuples):
    def make_bound(x, lb, ub):
        return logical_and(lb <= x, x <= ub)

    return reduce((lambda f, item: logical_and(f, make_bound(*item))), tuples,
                  Formula.True())


class CavTest(unittest.TestCase):
    def setUp(self):
        self.startTime = time.time()
        self.config = make_default_config()

    def tearDown(self):
        t = time.time() - self.startTime
        print "%-60s: %.3f" % (self.id(), t)


class UnconstrainedOptimizationTest(CavTest):
    def test_Ackley(self):
        domain = make_domain([(x, -5, 5), (y, -5, 5)])

        def objective(x, y):
            return (-20 * exp(-0.2 * sqrt(0.5 * (x**2 + y**2))) - exp(
                0.5 * (cos(2 * 3.141592 * x) + cos(2 * 3.141592 * y))) +
                2.71828182846 + 20)

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = 0.0
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    def test_Aluffi_Pentini(self):
        domain = make_domain([(x1, -10, 10), (x2, -10, 10)])

        def objective(x1, x2):
            return 0.25 * x1**4 - 0.5 * x1**2 + 0.1 * x1 + 0.5 * x2**2

        sol = Minimize(objective(x1, x2), domain, self.config)
        known_minimum = -0.3523
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x1].mid(), sol[x2].mid()),
            known_minimum,
            delta=self.config.precision)

    def test_Beale(self):
        domain = make_domain([(x, -4.5, 4.5), (y, -4.5, 4.5)])

        def objective(x, y):
            return ((1.5 - x + x * y)**2 + (2.25 - x + x * (y**2))**2 +
                    (2.625 - x + x * (y**3))**2)

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = 0
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()),
            known_minimum,
            delta=self.config.precision)

    def test_Bohachevsky1(self):
        domain = make_domain([(x, -100, 100), (y, -100, 100)])

        def objective(x, y):
            return x**2 + 2 * y**2 - 0.3 * cos(3 * 3.141592 * x) - 0.4 * cos(
                4 * 3.141592 * y) + 0.7

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = 0
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    def test_Booth(self):
        domain = make_domain([(x, -10, 10), (y, -10, 10)])

        def objective(x, y):
            return (x + 2 * y - 7)**2 + (2 * x + y - 5)**2

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = 0
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()),
            known_minimum,
            delta=self.config.precision)

    def test_Brent(self):
        domain = make_domain([(x, -10, 10), (y, -10, 10)])

        def objective(x, y):
            return (x + 10)**2 + (y + 10)**2 + exp(-1 * x**2 - y**2)

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = 0
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    def test_Bukin6(self):
        domain = make_domain([(x, -15, 15), (y, -3, 3)])

        def objective(x, y):
            return 100 * sqrt(abs(y - 0.01 * x**2)) + 0.01 * abs(x + 10)

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = 0
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    def test_Cross_in_Tray(self):
        domain = make_domain([(x, -10, 10), (y, -10, 10)])

        def objective(x, y):
            return -0.0001 * (abs(
                sin(x) * sin(y) * exp(abs(100 - sqrt(x**2 + y**2) / 3.141592)))
                + 1)**0.1

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = -2.06261
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    def test_Cross_in_Tray(self):
        domain = make_domain([(x, -10, 10), (y, -10, 10)])

        def objective(x, y):
            return -0.0001 * (abs(
                sin(x) * sin(y) * exp(abs(100 - sqrt(x**2 + y**2) / 3.141592)))
                + 1)**0.1

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = -2.06261
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    def test_Easom(self):
        domain = make_domain([(x, -100, 100), (y, -100, 100)])

        def objective(x, y):
            return -cos(x) * cos(y) * exp(-(
                (x - 3.141592)**2 + (y - 3.141592)**2))

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = -1
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    # DELTA DOESN'T HOLD
    @unittest.expectedFailure
    def test_EggHolder(self):
        domain = make_domain([(x, -512, 512), (y, -512, 512)])

        def objective(x, y):
            return -(y + 47) * sin(sqrt(abs(x / 2 + y + 47))) - x * sin(
                sqrt(abs(x - y - 47)))

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = -959.6407
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    # SLOW
    def test_Holder_Table2(self):
        domain = make_domain([(x, -10, 10), (y, -10, 10)])

        def objective(x, y):
            return -abs(
                sin(x) * cos(y) * exp(abs(1 - sqrt(x**2 + y**2) / 3.141592)))

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = -19.2085
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    def test_Levi_N13(self):
        domain = make_domain([(x, -10, 10), (y, -10, 10)])

        def objective(x, y):
            return (sin(3 * 3.141592 * x))**2 + (x - 1)**2 * (
                1 + (sin(3 * 3.141592 * y))**2) + (y - 1)**2 * (
                    1 + (sin(2 * 3.141592 * y))**2)

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = 0
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    def test_Schaffer_F6(self):
        domain = make_domain([(x, -100, 100), (y, -100, 100)])

        def objective(x, y):
            return 0.5 + ((sin(x**2 - y**2))**2 - 0.5) / (1 + 0.001 *
                                                          (x**2 + y**2))**2

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = 0
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    def test_Testtube_Holder(self):
        domain = make_domain([(x, -10, 10), (y, -10, 10)])

        def objective(x1, x2):
            return -4 * (
                sin(x1) * cos(x2) * exp(abs(cos((x1**2 + x2**2) / 200))))

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = -10.872300
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    def test_W_Wavy(self):
        domain = make_domain([(x, -3, 3), (y, -3, 3)])

        def objective(x1, x2):
            return 1 - 0.5 * ((cos(10 * x1) * exp(-x1**2 / 2)) +
                              (cos(10 * x2) * exp(-x2**2 / 2)))

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = 0.0
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    def test_Zettl(self):
        domain = make_domain([(x, -5, 10), (y, -5, 10)])

        def objective(x1, x2):
            return (x1**2 + x2**2 - 2 * x1)**2 + 0.25 * x1

        sol = Minimize(objective(x, y), domain, self.config)
        known_minimum = -0.003791
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()),
            known_minimum,
            delta=self.config.precision)


class ConstrainedOptimizationTest(CavTest):
    def test_Rosenbrock_Cubic(self):
        domain = make_domain([(x, -1.5, 1.5), (y, -0.5, 2.5)])

        def objective(x, y):
            return (1 - x)**2 + 100 * (y - x**2)**2

        constraints = logical_and(domain, (x - 1)**3 - y + 1 < 0,
                                  x + y - 2 < 0)

        sol = Minimize(objective(x, y), constraints, self.config)
        known_minimum = 0.0
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()),
            known_minimum,
            delta=self.config.precision)

    def test_Rosenbrock_Disk(self):
        domain = make_domain([(x, -1.5, 1.5), (y, -1.5, 1.5)])

        def objective(x, y):
            return (1 - x)**2 + 100 * (y - x**2)**2

        constraints = logical_and(domain, x**2 + y**2 < 2)

        sol = Minimize(objective(x, y), constraints, self.config)
        known_minimum = 0.0
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()),
            known_minimum,
            delta=self.config.precision)

    def test_Mishra_Bird(self):
        domain = make_domain([(x, -10, 0.0), (y, -6.5, 0.0)])

        def objective(x, y):
            return sin(y) * exp((1 - cos(x))**2) + cos(x) * exp(
                (1 - sin(y))**2) + (x - y)**2

        constraints = logical_and(domain, (x + 5)**2 + (y + 5)**2 < 25)

        sol = Minimize(objective(x, y), constraints, self.config)
        known_minimum = -106.7645367
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    # DELTA DOESN'T HOLD
    @unittest.expectedFailure
    def test_Townsend(self):
        domain = make_domain([(x, -2.25, 2.5), (y, -2.5, 1.75)])

        def objective(x, y):
            return -(cos((x - 0.1) * y))**2 - x * sin(3 * x + y)

        constraints = logical_and(
            domain, x**2 + y**2 <
            (2 * cos(atan2(x, y)) - 0.5 * cos(2 * atan2(x, y)) -
             0.25 * cos(3 * atan2(x, y)) - 0.125 * cos(4 * atan2(x, y)))**2 +
            (2 * sin(atan2(x, y)))**2)

        sol = Minimize(objective(x, y), constraints, self.config)
        known_minimum = -2.0239884
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()).Evaluate(),
            known_minimum,
            delta=self.config.precision)

    # DELTA DOESN'T HOLD
    @unittest.expectedFailure
    def test_Simionescu(self):
        domain = make_domain([(x, -1.25, 1.25), (y, -1.25, 1.25)])

        def objective(x, y):
            return 0.1 * x * y

        constraints = logical_and(domain, x**2 + y**2 <=
                                  (1 + 0.2 * cos(8 * atan(x / y)))**2)

        sol = Minimize(objective(x, y), constraints, self.config)
        known_minimum = -0.072625
        self.assertIsNotNone(sol)
        self.assertAlmostEqual(
            objective(sol[x].mid(), sol[y].mid()),
            known_minimum,
            delta=self.config.precision)


if __name__ == '__main__':
    unittest.main()
