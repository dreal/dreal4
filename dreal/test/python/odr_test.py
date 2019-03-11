from __future__ import absolute_import, division, print_function

import unittest

import dreal
import dreal._odr_test_module_py as odr_test_module


class TestODR(unittest.TestCase):
    def test_variable(self):
        x1 = dreal.Variable('x')
        x2 = odr_test_module.new_variable('x')
        self.assertNotEqual(x1.get_id(), x2.get_id())


if __name__ == '__main__':
    unittest.main(verbosity=0)
