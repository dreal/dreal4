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

import math
import unittest


def ExtractMidPoint(box):
    answers = {}
    for key, interval in box.items():
        answers[key] = interval.mid()
    return answers


class ApiTest(unittest.TestCase):
    def test_linear_optimization(self):
        x = Variable("x")
        y = Variable("y")
        constraints = And(
            x + 1.5 * y <= 750,
            2 * x + 3 * y <= 1500,
            2 * x + y <= 1000,
            x >= 0,
            y >= 0,
        )

        objective = 50 * x + 40 * y
        result = Minimize(-objective, constraints, 0.00001)
        objective_result = objective.Evaluate(ExtractMidPoint(result))
        self.assertAlmostEqual(objective_result, 28750, places=3)

    def test_minimize(self):
        eps = 0.001

        innerLeft = Variable("inner_left")
        innerRight = Variable("inner_right")
        innerWidth = Variable("in_width")
        innerCenter = Variable("in_center")
        outterLeft = Variable("out_left")
        outterRight = Variable("out_right")
        outterWidth = Variable("out_width")
        outterCenter = Variable("out_center")

        constraints = And(
            innerLeft <= innerRight,
            outterLeft <= outterRight,
            outterLeft <= innerLeft,
            outterRight >= innerRight,
            outterLeft >= 0,
            outterRight <= 255,

            # (2 * innerCenter) == (innerLeft + innerRight),
            -eps <= (innerLeft + innerRight) - (2 * innerCenter),
            (innerLeft + innerRight) - (2 * innerCenter) <= eps,

            # innerWidth == ( - innerLeft + innerRight),
            -eps <= (-innerLeft + innerRight) - innerWidth,
            (-innerLeft + innerRight) - innerWidth <= eps,

            # (2 * outterCenter) == (outterLeft + outterRight),
            -eps <= (outterLeft + outterRight) - (2 * outterCenter),
            (outterLeft + outterRight) - (2 * outterCenter) <= eps,

            # outterWidth == ( - outterLeft + outterRight),
            -eps <= (-outterLeft + outterRight) - outterWidth,
            (-outterLeft + outterRight) - outterWidth <= eps,

            # outterCenter == innerCenter,
            -eps <= innerCenter - outterCenter,
            innerCenter - outterCenter <= eps,

            # outterLeft == 38,
            38 - eps <= outterLeft,
            outterLeft <= 38 + eps,

            # outterRight == 182,
            182 - eps <= outterRight,
            outterRight <= 182 + eps,
        )
        objective = (outterWidth - innerWidth)

        result = Minimize(objective, constraints, 0.001)
        answers = {}
        for key, interval in result.items():
            answers[key] = interval.mid()

        objective_output = objective.Evaluate(answers)
        print("Objective:", objective_output)

        self.assertAlmostEqual(objective_output, 0, places=1)


if __name__ == '__main__':
    unittest.main()
