# -*- coding: utf-8 -*-
from __future__ import absolute_import
from __future__ import division
from __future__ import print_function

from dreal import *

import unittest


class LogicTest(unittest.TestCase):
    def test_logic(self):
        self.assertEqual(str(Logic.QF_NRA), "Logic.QF_NRA")
        self.assertEqual(str(Logic.QF_NRA_ODE), "Logic.QF_NRA_ODE")
        self.assertEqual(str(Logic.QF_LRA), "Logic.QF_LRA")
        self.assertEqual(str(Logic.QF_RDL), "Logic.QF_RDL")


if __name__ == '__main__':
    unittest.main()
