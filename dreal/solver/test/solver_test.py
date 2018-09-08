#!/usr/bin/env python
# -*- coding: utf-8 -*-
from dreal.solver import Config
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


if __name__ == '__main__':
    unittest.main()
