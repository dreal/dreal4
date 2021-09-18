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

from dreal import (Config, Variable, Context, Logic, cos, sin)

import unittest


class ConfigTest(unittest.TestCase):
    def test_precision(self):
        c = Config()
        c.precision = 0.0001
        self.assertEqual(c.precision, 0.0001)
        c.precision = 0.01
        self.assertEqual(c.precision, 0.01)

    def test_use_polytope(self):
        c = Config()
        c.use_polytope = False
        self.assertFalse(c.use_polytope)
        c.use_polytope = True
        self.assertTrue(c.use_polytope)

    def test_use_polytope_in_forall(self):
        c = Config()
        c.use_polytope_in_forall = False
        self.assertFalse(c.use_polytope_in_forall)
        c.use_polytope_in_forall = True
        self.assertTrue(c.use_polytope_in_forall)

    def test_use_worklist_fixpoint(self):
        c = Config()
        c.use_worklist_fixpoint = False
        self.assertFalse(c.use_worklist_fixpoint)
        c.use_worklist_fixpoint = True
        self.assertTrue(c.use_worklist_fixpoint)

    def test_use_local_optimization(self):
        c = Config()
        c.use_local_optimization = False
        self.assertFalse(c.use_local_optimization)
        c.use_local_optimization = True
        self.assertTrue(c.use_local_optimization)


x = Variable("x")
y = Variable("y")
z = Variable("z")


class ContextTest(unittest.TestCase):
    def test_sat(self):
        ctx = Context()
        ctx.SetLogic(Logic.QF_NRA)
        ctx.DeclareVariable(x, -10, 10)
        ctx.DeclareVariable(y, -10, 10)
        ctx.Assert(x == y + 5)
        ctx.Assert(y == 2)
        result = ctx.CheckSat()
        self.assertTrue(result)
        self.assertEqual(result[y].mid(), 2)
        self.assertEqual(result[x].mid(), 2 + 5)
        ctx.Exit()

    def test_unsat(self):
        ctx = Context()
        ctx.SetLogic(Logic.QF_NRA)
        x = Variable("x")
        y = Variable("y")
        ctx.DeclareVariable(x, -10, 10)
        ctx.DeclareVariable(y, -10, 10)
        ctx.Assert(x == y + 5)
        ctx.Assert(y == x - 3)
        result = ctx.CheckSat()
        self.assertFalse(result)
        ctx.Exit()

    def test_push_pop(self):
        ctx = Context()
        ctx.SetLogic(Logic.QF_NRA)
        x = Variable("x")
        y = Variable("y")
        ctx.DeclareVariable(x)
        ctx.SetInterval(x, -10, 10)
        ctx.DeclareVariable(y, -10, 10)
        ctx.Assert(x == y + 5)
        ctx.Push(1)
        ctx.Assert(y == x - 3)
        result = ctx.CheckSat()
        self.assertFalse(result)
        ctx.Pop(1)
        result = ctx.CheckSat()
        self.assertTrue(result)
        ctx.Exit()
        self.assertTrue(ctx.box)

    def test_config(self):
        ctx = Context()
        config1 = ctx.config
        self.assertEqual(config1.precision, 0.001)
        config1.precision = 0.0001
        self.assertEqual(ctx.config.precision, 0.0001)

    # TODO(soonho): Enable this by adding python binding for DynamicBitset
    # def test_brancher(self):
    #     self.branch_variables = []

    #     def MyBrancher(box, active_set, left, right):
    #         def FindMaxDiam(box, active_set):
    #             """Returns the dimension with the largest diameter"""
    #             max_diam = 0.0
    #             max_diam_idx = -1
    #             for var_i in active_set:
    #                 iv_i = box[var_i]
    #                 diam_i = iv_i.diam()
    #                 if diam_i > max_diam and iv_i.is_bisectable():
    #                     max_diam = diam_i
    #                     max_diam_idx = var_i
    #             return max_diam_idx

    #         branching_dim = FindMaxDiam(box, active_set)
    #         if branching_dim >= 0:
    #             (b1, b2) = box.bisect(branching_dim)
    #             left.set(b1)
    #             right.set(b2)
    #             self.branch_variables.append(box.variable(branching_dim))
    #             return branching_dim
    #         return -1

    #     ctx = Context()
    #     ctx.config.brancher = MyBrancher
    #     ctx.SetLogic(Logic.QF_NRA)
    #     ctx.DeclareVariable(x, -10, 10)
    #     ctx.DeclareVariable(y, -10, 10)
    #     ctx.Assert(cos(x) < sin(y))
    #     result = ctx.CheckSat()
    #     self.assertTrue(result)
    #     self.assertEqual(self.branch_variables, [x, y, x, y, x, y, x])
    #     ctx.Exit()

    def test_version(self):
        # Simply check if we can do this without checking the version
        # string.
        self.assertTrue(Context.version)


if __name__ == '__main__':
    unittest.main()
