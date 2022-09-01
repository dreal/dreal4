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

import unittest


class LogicTest(unittest.TestCase):
    def test_logic(self):
        self.assertEqual(str(Logic.ALL), "Logic.ALL")
        self.assertEqual(str(Logic.QF_LIA), "Logic.QF_LIA")
        self.assertEqual(str(Logic.QF_LIRA), "Logic.QF_LIRA")
        self.assertEqual(str(Logic.QF_LRA), "Logic.QF_LRA")
        self.assertEqual(str(Logic.QF_NIA), "Logic.QF_NIA")
        self.assertEqual(str(Logic.QF_NIAT), "Logic.QF_NIAT")
        self.assertEqual(str(Logic.QF_NIRA), "Logic.QF_NIRA")
        self.assertEqual(str(Logic.QF_NIRAT), "Logic.QF_NIRAT")
        self.assertEqual(str(Logic.QF_NRA), "Logic.QF_NRA")
        self.assertEqual(str(Logic.QF_NRAT), "Logic.QF_NRAT")
        self.assertEqual(str(Logic.QF_RDL), "Logic.QF_RDL")


if __name__ == '__main__':
    unittest.main()
