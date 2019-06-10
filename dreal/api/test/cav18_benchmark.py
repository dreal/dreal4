#!/usr/bin/env python
# -*- coding: utf-8 -*-
# ----------------------------------------------------------------------
# Optimization Benchmark in the following paper
# ----------------------------------------------------------------------
# Delta-Decision Procedures for Exists-Forall Problems over the Reals
# Soonho Kong, Armando Solar-Lezama, and Sicun Gao
# In CAV (International Conference on Computer Aided Verification) 2018
# ----------------------------------------------------------------------
from dreal import *
from functools import reduce
import math
import time
import unittest
import argparse
import sys

local_optimization = False
precision = 0.0001
number_of_jobs = 1


def make_config():
    global local_optimization
    global precision
    global number_of_jobs
    config = Config()
    config.precision = precision
    config.use_local_optimization = local_optimization
    config.number_of_jobs = number_of_jobs
    return config


def make_domain(tuples):
    def make_bound(name_of_var, lb, ub):
        v = Variable(name_of_var)
        return (v, And(lb <= v, v <= ub))

    def reducer(vars_bounds, item):
        (var, bound) = make_bound(*item)
        vars = vars_bounds[0]
        bounds = vars_bounds[1]
        return (vars + [var], And(bounds, bound))

    return reduce((lambda vars_bounds, item: reducer(vars_bounds, item)),
                  tuples, ([], Formula.TRUE()))


def compute_min(objective, box, vars):
    v = objective(*[box[var].mid() for var in vars])
    if (type(v) is Expression):
        return v.Evaluate()
    else:
        return v


def output_string(suite_name, test_name, test_time, global_min, found_min, opt,
                  precision):
    print("| %-28s | %-20s | %10s | %10s | %10s | %10s | %10s |" %
          (suite_name, test_name, test_time, global_min, found_min, opt,
           precision))


def output(suite_name, test_name, test_time, global_min, found_min, opt,
           precision):
    output_string(suite_name, test_name, "%10.4f" % test_time,
                  "%10.5f" % global_min, "%10.5f" % found_min, opt,
                  "%10.3E" % precision)


output_string("Suite Name", "Test Name", "Time (s)", "Global Min", "Found Min",
              "Local Opt", "Delta")

print("-" * 120)


class CavTest(unittest.TestCase):
    def setUp(self):
        self.startTime = time.time()
        self.config = make_config()

    def tearDown(self):
        test_time = time.time() - self.startTime
        if self.config.use_local_optimization:
            opt_string = "YES"
        else:
            opt_string = "NO"
        test_suite_name = self.__class__.__name__[:-4]
        test_name = "_".join(self._testMethodName.split("_")[1:])
        output(test_suite_name, test_name, test_time, self.global_min,
               self.found_min, opt_string, self.config.precision)


class UnconstrainedOptimizationTest(CavTest):
    def test_01_Ackley_2D(self):
        (vars, domain) = make_domain([("x", -5, 5), ("y", -5, 5)])

        def objective(x, y):
            return (-20 * exp(-0.02 * sqrt(0.5 * (x**2 + y**2))) - exp(
                0.5 * (cos(2 * math.pi * x) + cos(2 * math.pi * y))) + math.e +
                    20)

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = 0.0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_02_Ackley_4D(self):
        (vars, domain) = make_domain([
            ("x1", -5, 5),
            ("x2", -5, 5),
            ("x3", -5, 5),
            ("x4", -5, 5),
        ])

        def objective(x1, x2, x3, x4):
            return (-20 * exp(-0.02 * sqrt(1.0 / 4.0 *
                                           (x1**2 + x2**2 + x3**2 + x4**2))) -
                    exp(1.0 / 4.0 *
                        (cos(2 * math.pi * x1) + cos(2 * math.pi * x2) + cos(
                            2 * math.pi * x3) + cos(2 * math.pi * x4))) +
                    math.e + 20)

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = 0.0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_03_Aluffi_Pentini(self):
        (vars, domain) = make_domain([("x1", -10, 10), ("x2", -10, 10)])

        def objective(x1, x2):
            return 0.25 * x1**4 - 0.5 * x1**2 + 0.1 * x1 + 0.5 * x2**2

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = -0.3523
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_04_Beale(self):
        (vars, domain) = make_domain([("x", -4.5, 4.5), ("y", -4.5, 4.5)])

        def objective(x, y):
            return ((1.5 - x + x * y)**2 + (2.25 - x + x * (y**2))**2 +
                    (2.625 - x + x * (y**3))**2)

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = 0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_05_Bohachevsky1(self):
        (vars, domain) = make_domain([("x", -100, 100), ("y", -100, 100)])

        def objective(x, y):
            return x**2 + 2 * y**2 - 0.3 * cos(3 * math.pi * x) - 0.4 * cos(
                4 * math.pi * y) + 0.7

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = 0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_06_Booth(self):
        (vars, domain) = make_domain([("x", -10, 10), ("y", -10, 10)])

        def objective(x, y):
            return (x + 2 * y - 7)**2 + (2 * x + y - 5)**2

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = 0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_07_Brent(self):
        (vars, domain) = make_domain([("x", -10, 10), ("y", -10, 10)])

        def objective(x, y):
            return (x + 10)**2 + (y + 10)**2 + exp(-1 * x**2 - y**2)

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = 0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_08_Bukin6(self):
        (vars, domain) = make_domain([("x", -15, 15), ("y", -3, 3)])

        def objective(x, y):
            return 100 * sqrt(abs(y - 0.01 * x**2)) + 0.01 * abs(x + 10)

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = 0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_09_Cross_in_Tray(self):
        (vars, domain) = make_domain([("x", -10, 10), ("y", -10, 10)])

        def objective(x, y):
            return -0.0001 * (abs(
                sin(x) * sin(y) * exp(abs(100 - sqrt(x**2 + y**2) / math.pi)))
                              + 1)**0.1

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = -2.06261
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_10_Easom(self):
        (vars, domain) = make_domain([("x", -100, 100), ("y", -100, 100)])

        def objective(x, y):
            return -cos(x) * cos(y) * exp(-(
                (x - math.pi)**2 + (y - math.pi)**2))

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = -1
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_11_EggHolder(self):
        (vars, domain) = make_domain([("x", -512, 512), ("y", -512, 512)])

        def objective(x1, x2):
            return -(x2 + 47) * sin(sqrt(abs(x2 + x1 / 2.0 + 47))) - x1 * sin(
                sqrt(abs(x1 - (x2 + 47))))

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = -959.6407
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 5)

    # SLOW
    def test_12_Holder_Table2(self):
        (vars, domain) = make_domain([("x", -10, 10), ("y", -10, 10)])

        def objective(x, y):
            return -abs(
                sin(x) * cos(y) * exp(abs(1 - sqrt(x**2 + y**2) / math.pi)))

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = -19.2085
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_13_Levi_N13(self):
        (vars, domain) = make_domain([("x", -10, 10), ("y", -10, 10)])

        def objective(x, y):
            return (sin(3 * math.pi * x)
                    )**2 + (x - 1)**2 * (1 + (sin(3 * math.pi * y))**2) + (
                        y - 1)**2 * (1 + (sin(2 * math.pi * y))**2)

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = 0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_14_Ripple1(self):
        (vars, domain) = make_domain([("x1", 0, 1.0), ("x2", 0, 1.0)])

        def objective(x1, x2):
            t1 = -1 * exp(-2 * log(2) * ((x1 - 0.1) / 0.8)**2) * (
                sin(5 * math.pi * x1)**6 + 0.1 * cos(500 * math.pi * x1)**2)
            t2 = -1 * exp(-2 * log(2) * ((x2 - 0.1) / 0.8)**2) * (
                sin(5 * math.pi * x2)**6 + 0.1 * cos(500 * math.pi * x2)**2)
            return t1 + t2

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = -2.2
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_15_Schaffer_F6(self):
        (vars, domain) = make_domain([("x", -100, 100), ("y", -100, 100)])

        def objective(x, y):
            return 0.5 + (
                (sin(x**2 - y**2))**2 - 0.5) / (1 + 0.001 * (x**2 + y**2))**2

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = 0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_16_Testtube_Holder(self):
        (vars, domain) = make_domain([("x", -10, 10), ("y", -10, 10)])

        def objective(x1, x2):
            return -4 * (
                sin(x1) * cos(x2) * exp(abs(cos((x1**2 + x2**2) / 200))))

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = -10.872300
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_17_Trefethen(self):
        (vars, domain) = make_domain([("x", -10, 10), ("y", -10, 10)])

        def objective(x1, x2):
            return exp(sin(50 * x1)) + sin(60 * exp(x2)) + sin(
                70 * sin(x1)) + sin(sin(80 * x2)) - sin(
                    10 * (x1 + x2)) + 0.25 * (x1**2 + x2**2)

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = -3.30686865
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_18_W_Wavy(self):
        (vars, domain) = make_domain([("x", -3, 3), ("y", -3, 3)])

        def objective(x1, x2):
            return 1 - 0.5 * ((cos(10 * x1) * exp(-x1**2 / 2)) +
                              (cos(10 * x2) * exp(-x2**2 / 2)))

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = 0.0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_19_Zettl(self):
        (vars, domain) = make_domain([("x", -5, 10), ("y", -5, 10)])

        def objective(x1, x2):
            return (x1**2 + x2**2 - 2 * x1)**2 + 0.25 * x1

        sol = Minimize(objective(*vars), domain, self.config)
        self.global_min = -0.003791
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)


class ConstrainedOptimizationTest(CavTest):
    def test_01_Rosenbrock_Cubic(self):
        (vars, domain) = make_domain([("x", -1.5, 1.5), ("y", -0.5, 2.5)])
        [x, y] = vars

        def objective(x, y):
            return (1 - x)**2 + 100 * (y - x**2)**2

        constraints = And(domain, (x - 1)**3 - y + 1 < 0, x + y - 2 < 0)

        sol = Minimize(objective(*vars), constraints, self.config)
        self.global_min = 0.0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_02_Rosenbrock_Disk(self):
        (vars, domain) = make_domain([("x", -1.5, 1.5), ("y", -1.5, 1.5)])
        [x, y] = vars

        def objective(x, y):
            return (1 - x)**2 + 100 * (y - x**2)**2

        constraints = And(domain, x**2 + y**2 < 2)

        sol = Minimize(objective(*vars), constraints, self.config)
        self.global_min = 0.0
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_03_Mishra_Bird(self):
        (vars, domain) = make_domain([("x", -10, 0.0), ("y", -6.5, 0.0)])
        [x, y] = vars

        def objective(x, y):
            return sin(y) * exp((1 - cos(x))**2) + cos(x) * exp(
                (1 - sin(y))**2) + (x - y)**2

        constraints = And(domain, (x + 5)**2 + (y + 5)**2 < 25)

        sol = Minimize(objective(*vars), constraints, self.config)
        self.global_min = -106.7645367
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_04_Townsend(self):
        (vars, domain) = make_domain([("x", -2.25, 2.5), ("y", -2.5, 1.75)])
        [x, y] = vars

        def objective(x, y):
            return -(cos((x - 0.1) * y))**2 - x * sin(3 * x + y)

        constraints = And(
            domain, x**2 + y**2 <
            (2 * cos(atan2(x, y)) - 0.5 * cos(2 * atan2(x, y)) -
             0.25 * cos(3 * atan2(x, y)) - 0.125 * cos(4 * atan2(x, y)))**2 +
            (2 * sin(atan2(x, y)))**2)

        sol = Minimize(objective(*vars), constraints, self.config)
        self.global_min = -2.0239884
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 2)

    def test_05_Simionescu(self):
        (vars, domain) = make_domain([("x", -1.25, 1.25), ("y", -1.25, 1.25)])
        [x, y] = vars

        def objective(x, y):
            return 0.1 * x * y

        constraints = And(domain,
                          x**2 + y**2 <= (1 + 0.2 * cos(8 * atan(x / y)))**2)

        sol = Minimize(objective(*vars), constraints, self.config)
        self.global_min = -0.072625
        self.assertIsNotNone(sol)
        self.found_min = compute_min(objective, sol, vars)
        self.assertAlmostEqual(
            self.found_min, self.global_min, delta=self.config.precision * 10)


def main():
    global local_optimization
    global precision
    global number_of_jobs

    parser = argparse.ArgumentParser(
        description="Run CAV'18 Optimization Benchmark")
    parser.add_argument(
        '--local-optimization',
        dest='local_optimization',
        action='store_true',
        default=False,
        help='Use local optimization')
    parser.add_argument(
        '--precision',
        dest='precision',
        action='store',
        default=0.0001,
        type=float,
        help='Precision')
    parser.add_argument(
        '--jobs',
        dest='number_of_jobs',
        action='store',
        default=1,
        type=int,
        help='number of jobs')
    parser.add_argument('unittest_args', nargs='*')
    args = parser.parse_args()
    local_optimization = args.local_optimization
    precision = args.precision
    number_of_jobs = args.number_of_jobs

    sys.argv[1:] = args.unittest_args
    unittest.main(verbosity=0)


if __name__ == '__main__':
    main()
