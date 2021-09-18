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
from __future__ import absolute_import, division, print_function

import math
import unittest

from dreal import (And, Expression, Formula, Iff, Implies, Not, Or, Variable,
                   Variables, acos, asin, atan, atan2, cos, cosh, exp, forall,
                   if_then_else, intersect, log, logical_imply, Max, Min, sin,
                   sinh, sqrt, tan, tanh)

x = Variable("x")
y = Variable("y")
z = Variable("z")
w = Variable("w")
a = Variable("a")
b = Variable("b")
c = Variable("c")
b1 = Variable("b1", Variable.Bool)
b2 = Variable("b2", Variable.Bool)

e_x = Expression(x)
e_y = Expression(y)


class SymbolicVariableTest(unittest.TestCase):
    def test_type(self):
        real_var = Variable("x", Variable.Real)
        self.assertEqual(real_var.get_type(), Variable.Real)
        int_var = Variable("x", Variable.Int)
        self.assertEqual(int_var.get_type(), Variable.Int)
        bool_var = Variable("x", Variable.Bool)
        self.assertEqual(bool_var.get_type(), Variable.Bool)
        binary_var = Variable("x", Variable.Binary)
        self.assertEqual(binary_var.get_type(), Variable.Binary)

    def test_addition(self):
        self.assertEqual(str(x + y), "(x + y)")
        self.assertEqual(str(x + 1), "(1 + x)")
        self.assertEqual(str(1 + x), "(1 + x)")

    def test_subtraction(self):
        self.assertEqual(str(x - y), "(x - y)")
        self.assertEqual(str(x - 1), "(-1 + x)")
        self.assertEqual(str(1 - x), "(1 - x)")

    def test_multiplication(self):
        self.assertEqual(str(x * y), "(x * y)")
        self.assertEqual(str(x * 1), "x")
        self.assertEqual(str(1 * x), "x")

    def test_division(self):
        self.assertEqual(str(x / y), "(x / y)")
        self.assertEqual(str(x / 1), "x")
        self.assertEqual(str(1 / x), "(1 / x)")

    def test_unary_operators(self):
        self.assertEqual(str(+x), "x")
        self.assertEqual(str(-x), "(-1 * x)")

    def test_relational_operators(self):
        # Variable rop float
        self.assertEqual(str(x >= 1), "(x >= 1)")
        self.assertEqual(str(x > 1), "(x > 1)")
        self.assertEqual(str(x <= 1), "(x <= 1)")
        self.assertEqual(str(x < 1), "(x < 1)")
        self.assertEqual(str(x == 1), "(x == 1)")
        self.assertEqual(str(x != 1), "(x != 1)")

        # float rop Variable
        self.assertEqual(str(1 < y), "(y > 1)")
        self.assertEqual(str(1 <= y), "(y >= 1)")
        self.assertEqual(str(1 > y), "(y < 1)")
        self.assertEqual(str(1 >= y), "(y <= 1)")
        self.assertEqual(str(1 == y), "(y == 1)")
        self.assertEqual(str(1 != y), "(y != 1)")

        # Variable rop Variable
        self.assertEqual(str(x < y), "(x < y)")
        self.assertEqual(str(x <= y), "(x <= y)")
        self.assertEqual(str(x > y), "(x > y)")
        self.assertEqual(str(x >= y), "(x >= y)")
        self.assertEqual(str(x == y), "(x == y)")
        self.assertEqual(str(x != y), "(x != y)")

    def test_repr(self):
        self.assertEqual(repr(x), "Variable('x')")

    def test_simplify(self):
        self.assertEqual(str(0 * (x + y)), "0")
        self.assertEqual(str(x + y - x - y), "0")
        self.assertEqual(str(x / x - 1), "0")
        self.assertEqual(str(x / x), "1")

    def test_expand(self):
        ex = 2 * (x + y)
        self.assertEqual(str(ex), "(2 * (x + y))")
        self.assertEqual(str(ex.Expand()), "(2 * x + 2 * y)")

    def test_pow(self):
        self.assertEqual(str(x**2), "pow(x, 2)")
        self.assertEqual(str(x**y), "pow(x, y)")
        self.assertEqual(str((x + 1)**(y - 1)), "pow((1 + x), (-1 + y))")

    def test_neg(self):
        self.assertEqual(str(-(x + 1)), "(-1 - x)")

    def test_logical(self):
        f1 = (x == 0)
        f2 = (y == 0)
        self.assertEqual(str(Not(f1)), "!((x == 0))")
        self.assertEqual(str(Implies(f1, f2)), str(Or(Not(f1), f2)))
        self.assertEqual(str(Iff(f1, f2)),
                         str(And(Implies(f1, f2), Implies(f2, f1))))

        # Test single-operand logical statements
        self.assertEqual(str(And(x >= 1)), "(x >= 1)")
        self.assertEqual(str(Or(x >= 1)), "(x >= 1)")
        # Test binary operand logical statements
        self.assertEqual(str(And(x >= 1, x <= 2)), "((x >= 1) and (x <= 2))")
        self.assertEqual(str(Or(x <= 1, x >= 2)), "((x >= 2) or (x <= 1))")
        # Test multiple operand logical statements
        self.assertEqual(str(And(x >= 1, x <= 2, y == 2)),
                         "((y == 2) and (x >= 1) and (x <= 2))")
        self.assertEqual(str(Or(x >= 1, x <= 2, y == 2)),
                         "((y == 2) or (x >= 1) or (x <= 2))")

    def test_logical2(self):
        self.assertEqual(str(And(b1, b2, Implies(b1, b2))),
                         "(b1 and b2 and (b2 or !(b1)))")
        self.assertEqual(str(Or(b1, b2, Implies(b1, b2))),
                         "(b1 or b2 or !(b1))")
        self.assertEqual(str(Not(b1)), "!(b1)")

    def test_functions_with_variable(self):
        self.assertEqual(str(log(x)), "log(x)")
        self.assertEqual(str(abs(x)), "abs(x)")
        self.assertEqual(str(exp(x)), "exp(x)")
        self.assertEqual(str(sqrt(x)), "sqrt(x)")
        self.assertEqual(str(pow(x, y)), "pow(x, y)")
        self.assertEqual(str(sin(x)), "sin(x)")
        self.assertEqual(str(cos(x)), "cos(x)")
        self.assertEqual(str(tan(x)), "tan(x)")
        self.assertEqual(str(asin(x)), "asin(x)")
        self.assertEqual(str(acos(x)), "acos(x)")
        self.assertEqual(str(atan(x)), "atan(x)")
        self.assertEqual(str(atan2(x, y)), "atan2(x, y)")
        self.assertEqual(str(sinh(x)), "sinh(x)")
        self.assertEqual(str(cosh(x)), "cosh(x)")
        self.assertEqual(str(tanh(x)), "tanh(x)")
        self.assertEqual(str(Min(x, y)), "min(x, y)")
        self.assertEqual(str(Max(x, y)), "max(x, y)")
        self.assertEqual(str(if_then_else(x > y, x, y)),
                         "(if (x > y) then x else y)")


class TestSymbolicVariables(unittest.TestCase):
    def test_default_constructor(self):
        variables = Variables()
        self.assertEqual(variables.size(), 0)
        self.assertTrue(variables.empty())

    def test_constructor_list(self):
        variables = Variables([x, y, z])
        self.assertEqual(variables.size(), 3)
        self.assertEqual(len(variables), 3)

    def test_to_string(self):
        variables = Variables([x, y, z])
        self.assertEqual(variables.to_string(), "{x, y, z}")
        self.assertEqual("{}".format(variables), "{x, y, z}")

    def test_repr(self):
        variables = Variables([x, y, z])
        self.assertEqual(repr(variables), '<Variables "{x, y, z}">')

    def test_insert1(self):
        variables = Variables()
        variables.insert(x)
        self.assertEqual(variables.size(), 1)

    def test_insert2(self):
        variables = Variables([x])
        variables.insert(Variables([y, z]))
        self.assertEqual(variables.size(), 3)

    def test_erase1(self):
        variables = Variables([x, y, z])
        count = variables.erase(x)
        self.assertEqual(count, 1)

    def test_erase2(self):
        variables1 = Variables([x, y, z])
        variables2 = Variables([w, z])
        count = variables1.erase(variables2)
        self.assertEqual(count, 1)
        self.assertEqual(variables1.size(), 2)

    def test_include(self):
        variables = Variables([x, y, z])
        self.assertTrue(variables.include(y))
        self.assertTrue(y in variables)
        self.assertFalse(w in variables)

    def test_subset_properties(self):
        variables1 = Variables([x, y, z])
        variables2 = Variables([x, y])
        self.assertFalse(variables1.IsSubsetOf(variables2))
        self.assertFalse(variables1.IsStrictSubsetOf(variables2))
        self.assertTrue(variables1.IsSupersetOf(variables2))
        self.assertTrue(variables1.IsStrictSupersetOf(variables2))

    def test_eq(self):
        variables1 = Variables([x, y, z])
        variables2 = Variables([x, y])
        self.assertFalse(variables1 == variables2)

    def test_lt(self):
        variables1 = Variables([x, y])
        variables2 = Variables([x, y, z])
        self.assertTrue(variables1 < variables2)

    def test_add(self):
        variables1 = Variables([x, y])
        variables2 = Variables([y, z])
        variables3 = variables1 + variables2  # [x, y, z]
        self.assertEqual(variables3.size(), 3)
        variables4 = variables1 + z  # [x, y, z]
        self.assertEqual(variables4.size(), 3)
        variables5 = x + variables1  # [x, y]
        self.assertEqual(variables5.size(), 2)

    def test_add_assignment(self):
        variables = Variables([x])
        variables += y
        self.assertEqual(variables.size(), 2)
        variables += Variables([x, z])
        self.assertEqual(variables.size(), 3)

    def test_sub(self):
        variables1 = Variables([x, y])
        variables2 = Variables([y, z])
        variables3 = variables1 - variables2  # [x]
        self.assertEqual(variables3, Variables([x]))
        variables4 = variables1 - y  # [x]
        self.assertEqual(variables4, Variables([x]))

    def test_sub_assignment(self):
        variables = Variables([x, y, z])
        variables -= y  # = [x, z]
        self.assertEqual(variables, Variables([x, z]))
        variables -= Variables([x])  # = [z]
        self.assertEqual(variables, Variables([z]))

    def test_intersect(self):
        variables1 = Variables([x, y, z])
        variables2 = Variables([y, w])
        variables3 = intersect(variables1, variables2)  # = [y]
        self.assertEqual(variables3, Variables([y]))

    def test_iter(self):
        variables = Variables([x, y, z])
        count = 0
        for var in variables:
            self.assertTrue(var in variables)
            count = count + 1
        self.assertEqual(count, len(variables))


class TestSymbolicExpression(unittest.TestCase):
    def test_addition(self):
        self.assertEqual(str(e_x + e_y), "(x + y)")
        self.assertEqual(str(e_x + y), "(x + y)")
        self.assertEqual(str(e_x + 1), "(1 + x)")
        self.assertEqual(str(x + e_y), "(x + y)")
        self.assertEqual(str(1 + e_x), "(1 + x)")

    def test_addition_assign(self):
        e = x
        e += e_y
        self.assertEqual(e, x + y)
        e += z
        self.assertEqual(e, x + y + z)
        e += 1
        self.assertEqual(e, x + y + z + 1)

    def test_subtract(self):
        self.assertEqual(str(e_x - e_y), "(x - y)")
        self.assertEqual(str(e_x - y), "(x - y)")
        self.assertEqual(str(e_x - 1), "(-1 + x)")
        self.assertEqual(str(x - e_y), "(x - y)")
        self.assertEqual(str(1 - e_x), "(1 - x)")

    def test_subtract_assign(self):
        e = x
        e -= e_y
        self.assertEqual(e, x - y)
        e -= z
        self.assertEqual(e, x - y - z)
        e -= 1
        self.assertEqual(e, x - y - z - 1)

    def test_multiplication(self):
        self.assertEqual(str(e_x * e_y), "(x * y)")
        self.assertEqual(str(e_x * y), "(x * y)")
        self.assertEqual(str(e_x * 1), "x")
        self.assertEqual(str(x * e_y), "(x * y)")
        self.assertEqual(str(1 * e_x), "x")

    def test_multiplication_assign(self):
        e = x
        e *= e_y
        self.assertEqual(e, x * y)
        e *= z
        self.assertEqual(e, x * y * z)
        e *= 1
        self.assertEqual(e, x * y * z)

    def test_division(self):
        self.assertEqual(str(e_x / e_y), "(x / y)")
        self.assertEqual(str(e_x / y), "(x / y)")
        self.assertEqual(str(e_x / 1), "x")
        self.assertEqual(str(x / e_y), "(x / y)")
        self.assertEqual(str(1 / e_x), "(1 / x)")

    def test_division_assign(self):
        e = x
        e /= e_y
        self.assertEqual(e, x / y)
        e /= z
        self.assertEqual(e, x / y / z)
        e /= 1
        self.assertEqual(e, x / y / z)

    def test_unary_operators(self):
        # self.assertEqual(str(+e_x), "x")
        self.assertEqual(str(-e_x), "(-1 * x)")

    def test_relational_operators(self):
        # Expression rop Expression
        self.assertEqual(str(e_x < e_y), "(x < y)")
        self.assertEqual(str(e_x <= e_y), "(x <= y)")
        self.assertEqual(str(e_x > e_y), "(x > y)")
        self.assertEqual(str(e_x >= e_y), "(x >= y)")
        self.assertEqual(str(e_x == e_y), "(x == y)")
        self.assertEqual(str(e_x != e_y), "(x != y)")

        # Expression rop Variable
        self.assertEqual(str(e_x < y), "(x < y)")
        self.assertEqual(str(e_x <= y), "(x <= y)")
        self.assertEqual(str(e_x > y), "(x > y)")
        self.assertEqual(str(e_x >= y), "(x >= y)")
        self.assertEqual(str(e_x == y), "(x == y)")
        self.assertEqual(str(e_x != y), "(x != y)")

        # Variable rop Expression
        self.assertEqual(str(x < e_y), "(x < y)")
        self.assertEqual(str(x <= e_y), "(x <= y)")
        self.assertEqual(str(x > e_y), "(x > y)")
        self.assertEqual(str(x >= e_y), "(x >= y)")
        self.assertEqual(str(x == e_y), "(x == y)")
        self.assertEqual(str(x != e_y), "(x != y)")

        # Expression rop float
        self.assertEqual(str(e_x < 1), "(x < 1)")
        self.assertEqual(str(e_x <= 1), "(x <= 1)")
        self.assertEqual(str(e_x > 1), "(x > 1)")
        self.assertEqual(str(e_x >= 1), "(x >= 1)")
        self.assertEqual(str(e_x == 1), "(x == 1)")
        self.assertEqual(str(e_x != 1), "(x != 1)")

        # float rop Expression
        self.assertEqual(str(1 < e_y), "(y > 1)")
        self.assertEqual(str(1 <= e_y), "(y >= 1)")
        self.assertEqual(str(1 > e_y), "(y < 1)")
        self.assertEqual(str(1 >= e_y), "(y <= 1)")
        self.assertEqual(str(1 == e_y), "(y == 1)")
        self.assertEqual(str(1 != e_y), "(y != 1)")

    def test_functions_with_float(self):
        v_x = 1.0
        v_y = 1.0
        self.assertEqual(abs(v_x), math.fabs(v_x))
        self.assertEqual(exp(v_x), math.exp(v_x))
        self.assertEqual(sqrt(v_x), math.sqrt(v_x))
        self.assertEqual(pow(v_x, v_y), v_x**v_y)
        self.assertEqual(sin(v_x), math.sin(v_x))
        self.assertEqual(cos(v_x), math.cos(v_x))
        self.assertEqual(tan(v_x), math.tan(v_x))
        self.assertEqual(asin(v_x), math.asin(v_x))
        self.assertEqual(acos(v_x), math.acos(v_x))
        self.assertEqual(atan(v_x), math.atan(v_x))
        self.assertEqual(atan2(v_x, v_y), math.atan2(v_x, v_y))
        self.assertEqual(sinh(v_x), math.sinh(v_x))
        self.assertEqual(cosh(v_x), math.cosh(v_x))
        self.assertEqual(tanh(v_x), math.tanh(v_x))
        self.assertEqual(Min(v_x, v_y), Min(v_x, v_y))
        self.assertEqual(Max(v_x, v_y), Max(v_x, v_y))
        self.assertEqual(
            if_then_else(Expression(v_x) > Expression(v_y), v_x, v_y),
            v_x if v_x > v_y else v_y)

    def test_functions_with_variable(self):
        self.assertEqual(str(abs(x)), "abs(x)")
        self.assertEqual(str(exp(x)), "exp(x)")
        self.assertEqual(str(sqrt(x)), "sqrt(x)")
        self.assertEqual(str(pow(x, y)), "pow(x, y)")
        self.assertEqual(str(sin(x)), "sin(x)")
        self.assertEqual(str(cos(x)), "cos(x)")
        self.assertEqual(str(tan(x)), "tan(x)")
        self.assertEqual(str(asin(x)), "asin(x)")
        self.assertEqual(str(acos(x)), "acos(x)")
        self.assertEqual(str(atan(x)), "atan(x)")
        self.assertEqual(str(atan2(x, y)), "atan2(x, y)")
        self.assertEqual(str(sinh(x)), "sinh(x)")
        self.assertEqual(str(cosh(x)), "cosh(x)")
        self.assertEqual(str(tanh(x)), "tanh(x)")
        self.assertEqual(str(Min(x, y)), "min(x, y)")
        self.assertEqual(str(Max(x, y)), "max(x, y)")
        self.assertEqual(str(if_then_else(x > y, x, y)),
                         "(if (x > y) then x else y)")

    def test_functions_with_expression(self):
        self.assertEqual(str(abs(e_x)), "abs(x)")
        self.assertEqual(str(exp(e_x)), "exp(x)")
        self.assertEqual(str(sqrt(e_x)), "sqrt(x)")
        self.assertEqual(str(pow(e_x, e_y)), "pow(x, y)")
        self.assertEqual(str(sin(e_x)), "sin(x)")
        self.assertEqual(str(cos(e_x)), "cos(x)")
        self.assertEqual(str(tan(e_x)), "tan(x)")
        self.assertEqual(str(asin(e_x)), "asin(x)")
        self.assertEqual(str(acos(e_x)), "acos(x)")
        self.assertEqual(str(atan(e_x)), "atan(x)")
        self.assertEqual(str(atan2(e_x, e_y)), "atan2(x, y)")
        self.assertEqual(str(sinh(e_x)), "sinh(x)")
        self.assertEqual(str(cosh(e_x)), "cosh(x)")
        self.assertEqual(str(tanh(e_x)), "tanh(x)")
        self.assertEqual(str(Min(e_x, e_y)), "min(x, y)")
        self.assertEqual(str(Max(e_x, e_y)), "max(x, y)")
        self.assertEqual(str(if_then_else(e_x > e_y, e_x, e_y)),
                         "(if (x > y) then x else y)")

    def test_differentiate(self):
        e = x * x
        self.assertEqual(e.Differentiate(x), 2 * x)

    def test_repr(self):
        self.assertEqual(repr(e_x), '<Expression "x">')

    def test_evaluate(self):
        env = {x: 3, y: 4}
        self.assertEqual((x + y).Evaluate(env), 7)

    def test_evaluate_partial(self):
        env = {x: 3}
        self.assertEqual((x + y).EvaluatePartial(env), 3 + y)

    def test_substitute(self):
        e = x + y
        self.assertEqual(e.Substitute(x, 1.0), 1.0 + y)
        self.assertEqual(e.Substitute(x, y), 2 * y)
        self.assertEqual(e.Substitute(x, x + 5), x + y + 5)

    def test_if_then_else(self):
        b = Variable("b", Variable.Bool)
        e = if_then_else(b, 5.0, 3.0)
        self.assertEqual(str(e), "(if b then 5 else 3)")

        with self.assertRaises(Exception) as context:
            if_then_else(x, 5.0, 3.0)
        print(context.exception)
        self.assertTrue("not a Boolean variable but used as a conditional" in
                        str(context.exception))

    def test_to_prefix(self):
        self.assertEqual((x + y).ToPrefix(), "(+ x y)")

    def test_equality(self):
        # Boolean Variable == Boolean Variable
        self.assertEqual(b1 == b2, Iff(b1, b2))
        # Boolean Variable == Formula
        self.assertEqual(b1 == (x > 3), Iff(b1, x > 3))
        # Formula == Boolean Variable
        self.assertEqual((x > 3) == b1, Iff(x > 3, b1))
        # Scalar Variable == Scalar Variable
        self.assertEqual(str(x == y), '(x == y)')
        # Scalar Variable == Expression
        self.assertEqual(str(x == (y + 3)), '(x == (3 + y))')
        # Expression == Scalar Variable
        self.assertEqual(str((3 + y) == x), '((3 + y) == x)')
        # Expression == Expression
        self.assertEqual(str((1 + x) == (2 + y)), '((1 + x) == (2 + y))')

    def test_inequality(self):
        # Boolean Variable != Boolean Variable
        self.assertEqual(b1 != b2, Not(Iff(b1, b2)))
        # Boolean Variable != Formula
        self.assertEqual(b1 != (x > 3), Not(Iff(b1, x > 3)))
        # Formula != Boolean Variable
        self.assertEqual((x > 3) != b1, Not(Iff(x > 3, b1)))
        # Scalar Variable != Scalar Variable
        self.assertEqual(str(x != y), '(x != y)')
        # Scalar Variable != Expression
        self.assertEqual(str(x != (y + 3)), '(x != (3 + y))')
        # Expression != Scalar Variable
        self.assertEqual(str((3 + y) != x), '((3 + y) != x)')
        # Expression != Expression
        self.assertEqual(str((1 + x) != (2 + y)), '((1 + x) != (2 + y))')


class TestSymbolicFormula(unittest.TestCase):
    def test_construct_formula_from_variable(self):
        a = Variable("a", Variable.Bool)
        b = Variable("a", Variable.Bool)
        self.assertEqual(str(logical_imply(Formula(a), Formula(b))),
                         "(a or !(a))")

    def test_get_free_variables(self):
        f = x > y
        self.assertEqual(f.GetFreeVariables(), Variables([x, y]))

    def test_evaluate(self):
        env = {x: 3, y: 4}
        self.assertEqual((x < y).Evaluate(env), True)
        self.assertEqual((x > y).Evaluate(env), False)

    def test_substitute_with_pair(self):
        f = x > y
        self.assertEqual(f.Substitute(y, y + 5), x > y + 5)
        self.assertEqual(f.Substitute(y, z), x > z)
        self.assertEqual(f.Substitute(y, 3), x > 3)

    def test_substitute_with_dict(self):
        f = x + y > z
        self.assertEqual(f.Substitute({x: x + 2, y: y + 3}), x + y + 5 > z)

    def test_to_string(self):
        f = x > y
        self.assertEqual(f.to_string(), "(x > y)")
        self.assertEqual("{}".format(f), "(x > y)")

    def test_equality_inequality_hash(self):
        f1 = x > y
        f2 = x > y
        f3 = x >= y
        self.assertTrue(f1.EqualTo(f2))
        self.assertEqual(hash(f1), hash(f2))
        self.assertTrue(f1 == f2)
        self.assertFalse(f1.EqualTo(f3))
        self.assertNotEqual(hash(f1), hash(f3))
        self.assertTrue(f1 != f3)

    def test_static_true_false(self):
        tt = Formula.TRUE()
        ff = Formula.FALSE()
        self.assertEqual(x == x, tt)
        self.assertEqual(x != x, ff)

    def test_repr(self):
        self.assertEqual(repr(x > y), '<Formula "(x > y)">')

    def test_forall(self):
        self.assertEqual(str(forall(Variables([x, y, z]), x == 0)),
                         "forall({x}. (x == 0))")
        self.assertEqual(str(forall([x, y, z], x == 0)),
                         "forall({x}. (x == 0))")

    def test_if_then_else(self):
        c = x > y
        f1 = x == 1.0
        f2 = y == 2.0
        f = if_then_else(c, f1, f2)
        env1 = {x: 2, y: 1}
        env2 = {x: 1, y: 2}
        env3 = {x: 1, y: 0}
        env4 = {x: 0, y: 1}
        self.assertEqual(f.Evaluate(env1), False)
        self.assertEqual(f.Evaluate(env2), True)
        self.assertEqual(f.Evaluate(env3), True)
        self.assertEqual(f.Evaluate(env4), False)

    def test_to_prefix(self):
        self.assertEqual((x > y).ToPrefix(), "(> x y)")


if __name__ == '__main__':
    unittest.main()
