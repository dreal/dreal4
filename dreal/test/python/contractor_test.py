# -*- coding: utf-8 -*-
#
#  Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
from __future__ import absolute_import, division, print_function

import unittest

from dreal import (
    Box,
    BuildContractor,
    Config,
    DynamicBitset,
    ContractorStatus,
    Interval,
    Variable,
    sin,
    cos,
    sqrt,
)

x = Variable("x")
y = Variable("y")
z = Variable("z")


class DynamicBitsetTest(unittest.TestCase):

    def test_all_any_none_set_get_reset_size(self):
        bitset = DynamicBitset(3)  # every bit is false.

        self.assertEqual(bitset.size(), 3)

        # bitset = 000
        self.assertFalse(bitset.all())
        self.assertFalse(bitset.any())
        self.assertTrue(bitset.none())

        # bitset = 010
        bitset.set(1, True)
        bitset.set(2, False)
        self.assertTrue(bitset.get(1))
        self.assertFalse(bitset.get(2))
        self.assertFalse(bitset.all())
        self.assertTrue(bitset.any())
        self.assertFalse(bitset.none())

        # bitset = 111
        bitset.set()  # sets all bits to true
        self.assertTrue(bitset.all())
        self.assertTrue(bitset.any())
        self.assertFalse(bitset.none())

        # bitset = 000
        bitset.reset()  # sets all bits to false
        self.assertFalse(bitset.all())
        self.assertFalse(bitset.any())
        self.assertTrue(bitset.none())

    def test_and(self):
        # bitset1 = 011 (Recall that it prints the last bit first)
        bitset1 = DynamicBitset(3)
        bitset1.set(0, True)
        bitset1.set(1, True)

        # bitset3 = 101
        bitset2 = DynamicBitset(3)
        bitset2.set(0, True)
        bitset2.set(2, True)

        bitset3 = bitset1 & bitset2
        # bitset3 = 001
        self.assertTrue(bitset3.get(0))
        self.assertFalse(bitset3.get(1))
        self.assertFalse(bitset3.get(2))

        # (bitset1 &= bitset2) == bitset3
        bitset1 &= bitset2
        self.assertEqual(bitset1, bitset3)

    def test_or(self):
        # bitset1 = 010
        bitset1 = DynamicBitset(3)
        bitset1.set(1, True)

        # bitset3 = 100
        bitset2 = DynamicBitset(3)
        bitset2.set(2, True)

        bitset3 = bitset1 | bitset2
        # bitset3 = 110
        self.assertFalse(bitset3.get(0))
        self.assertTrue(bitset3.get(1))
        self.assertTrue(bitset3.get(2))

        # (bitset1 |= bitset2) == bitset3
        bitset1 |= bitset2
        self.assertEqual(bitset1, bitset3)

    def test_str(self):
        # bitset1 = 010
        bitset1 = DynamicBitset(3)
        bitset1.set(1, True)
        self.assertEqual(str(bitset1), "010")


class ContractorStatusTest(unittest.TestCase):

    def test_box(self):
        # Set up a box
        box = Box([x, y])
        box[x] = Interval(-1, 1)
        box[y] = Interval(-1, 1)

        cs = ContractorStatus(box)
        self.assertEqual(box, cs.box())
        self.assertEqual(box, cs.mutable_box())

        # Get a box from this ContractorStatus and modify the local
        # copy.
        box_copy = cs.box()
        box_copy[x] = Interval(3, 4)
        # This is a local copy, so the modification does not affect
        # the box in the ContractorStatus.
        self.assertNotEqual(box_copy, cs.box())

        # Get a reference to the box in the ContractorStatus and modify it.
        box_reference = cs.mutable_box()
        box_reference[x] = Interval(3, 4)
        # The change should be made inside this ContractorStatus as well.
        self.assertEqual(box_reference, cs.box())

    def test_output(self):
        # Set up a box and a contractor status.
        box = Box([x, y])
        box[x] = Interval(-1, 1)
        box[y] = Interval(-1, 1)
        cs = ContractorStatus(box)

        # cs.output() == 00
        output = cs.output()
        self.assertEqual(output, cs.output())
        self.assertTrue(output.none())
        self.assertEqual(output.size(), 2)

        # cs.output() returns a copy of its output. So changing this
        # local copy does not change cs.output()
        output.set()  # output = 11
        self.assertEqual(str(cs.output()), "00")

        # cs.mutable_output() returns a reference to its output. So
        # changing this does change cs.output().
        mutable_output = cs.mutable_output()
        mutable_output.set()  # mutable_output = 11
        self.assertEqual(str(cs.output()), "11")

    def test_explanation(self):
        box = Box([x, y])
        self.assertEqual(str(box[x]), "[ ENTIRE ]")
        self.assertEqual(str(box[y]), "[ ENTIRE ]")

        config = Config()
        cs = ContractorStatus(box)

        # Constraints:
        #     -1 ≤ x ≤ 1
        #     -1 ≤ x ≤ 1
        #     sin(x) = y
        #     cos(x) = y
        #     x² + 1 = √y
        #     y² + 1 = √x
        constraints = [
            -1 <= x,
            x <= 1,
            -1 <= y,
            y <= 1,
            sin(x) == y,
            cos(x) == y,
            x * x + 1 == sqrt(y),
            y * y + 1 == sqrt(x),
        ]

        # Build a contractor based on the constraints, contractor
        # status, and dReal config.
        contractor = BuildContractor(constraints, cs, config)

        self.assertEqual(str(cs.box()[x]), "[-1, 1]")
        self.assertEqual(str(cs.box()[y]), "[-1, 1]")

        # Perform pruning.
        contractor.Prune(cs)

        # After pruning, the box is empty.
        self.assertTrue(cs.box().empty())

        # Extract the explanation of this UNSAT.
        #
        # This is a subset of the input constraints which contribute
        # to the reduction of the search space.
        explanation = cs.explanation()

        # sin(x) == y was used in this reduction.
        self.assertTrue((sin(x) == y) in explanation)

        # y² + 1 = √x was *not* used in this reduction.
        self.assertFalse((y * y + 1 == sqrt(x)) in explanation)


class ContractorTest(unittest.TestCase):

    def test_prune_input(self):
        box = Box([x, y, z])
        self.assertEqual(str(box[x]), "[ ENTIRE ]")
        self.assertEqual(str(box[y]), "[ ENTIRE ]")
        config = Config()
        cs = ContractorStatus(box)

        # Constraints:
        #     -1 ≤ x ≤ 1
        #     -1 ≤ x ≤ 1
        #     sin(x) = y
        #     cos(x) = y
        constraints = [
            -1 <= x,
            x <= 1,
            -1 <= y,
            y <= 1,
            sin(x) == y,
            cos(x) == y,
        ]

        # Build a contractor based on the constraints, contractor
        # status, and dReal config.
        contractor = BuildContractor(constraints, cs, config)

        # The input of this contractor is 011 meaning it uses the
        # variables x and y but not z.
        # Note that the dynamic bitset prints the last bit (z) first.
        self.assertEqual(str(contractor.input()), "011")

        # Calling BuildContractor will update the box inside of
        # cs.
        box = cs.box()
        self.assertEqual(str(box[x]), "[-1, 1]")
        self.assertEqual(str(box[y]), "[-1, 1]")

        # Before pruning, the output is 000.
        self.assertEqual(str(cs.output()), "000")

        # Perform pruning.
        contractor.Prune(cs)
        new_box = cs.box()

        # box != new_box
        self.assertNotEqual(box, new_box)

        # new_box[x] ⊂ box[x]
        self.assertTrue(new_box[x].is_strict_subset(box[x]))
        # new_box[y] ⊂ box[y]
        self.assertTrue(new_box[y].is_strict_subset(box[y]))
        # new_box[z] = box[z]
        self.assertTrue(new_box[z] == box[z])

        # new box is not empty.
        self.assertFalse(new_box.empty())

        # After pruning, the output is 011 (only x and y dimensions
        # were changed).
        self.assertEqual(str(cs.output()), "011")
        cs.mutable_output().reset()

        # We widen the box[x] and re-prune.
        cs.mutable_box()[x] = Interval(0.57, 1.10)
        contractor.Prune(cs)

        # As a result, it only changes x dimension.
        self.assertEqual(str(cs.output()), "001")


if __name__ == '__main__':
    unittest.main()
