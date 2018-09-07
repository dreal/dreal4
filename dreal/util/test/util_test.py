from dreal.util import Box
from dreal.util import Interval
from dreal.util import (exp, log, sqr, sqrt, pow, sin, cos, tan, asin, acos,
                        atan, atan2, sinh, cosh, tanh, root, abs, max, min,
                        sign, integer)
from dreal.symbolic import Variable
import unittest
import math

x = Variable("x")
y = Variable("y")
z = Variable("z")

inf = float("inf")


class IntervalTest(unittest.TestCase):
    def test_constructor(self):
        i1 = Interval()
        self.assertEqual(i1.lb(), -inf)
        self.assertEqual(i1.ub(), +inf)
        i2 = Interval(3, 4)
        self.assertEqual(i2.lb(), 3)
        self.assertEqual(i2.ub(), 4)
        i3 = Interval(5)
        self.assertEqual(i3.lb(), 5)
        self.assertEqual(i3.ub(), 5)

    def test_addition(self):
        i1 = Interval(3, 4)
        i2 = Interval(4, 5)
        self.assertEqual(i1 + i2, Interval(7, 9))
        self.assertEqual(i1 + 1, Interval(4, 5))
        self.assertEqual(1 + i1, Interval(4, 5))
        i1 += i2
        self.assertEqual(i1, Interval(7, 9))
        i1 += 1
        self.assertEqual(i1, Interval(8, 10))

    def test_subtraction(self):
        i1 = Interval(3, 4)
        i2 = Interval(4, 5)
        self.assertEqual(i1 - i2, Interval(-2, 0))
        self.assertEqual(i1 - 1, Interval(2, 3))
        self.assertEqual(1 - i1, Interval(-3, -2))
        i1 -= i2
        self.assertEqual(i1, Interval(-2, 0))
        i1 -= 1
        self.assertEqual(i1, Interval(-3, -1))

    def test_multiplication(self):
        i1 = Interval(3, 4)
        i2 = Interval(4, 5)
        self.assertEqual(i1 * i2, Interval(12, 20))
        self.assertEqual(i1 * 2, Interval(6, 8))
        self.assertEqual(2 * i1, Interval(6, 8))
        i1 *= i2
        self.assertEqual(i1, Interval(12, 20))
        i1 *= 2
        self.assertEqual(i1, Interval(24, 40))

    def test_division(self):
        i1 = Interval(3, 4)
        i2 = Interval(4, 5)
        self.assertEqual(i1 / i2, Interval(3.0 / 5.0, 4.0 / 4.0))
        self.assertEqual(i1 / 2, Interval(1.5, 2.0))
        self.assertAlmostEqual((2 / i1).lb(), 2 / 4.0)
        self.assertAlmostEqual((2 / i1).ub(), 2 / 3.0)
        i1 /= i2
        self.assertEqual(i1, Interval(3.0 / 5.0, 4.0 / 4.0))
        i1 /= 2
        self.assertEqual(i1, Interval(3.0 / 10.0, 4.0 / 8.0))

    def test_unary_minus(self):
        i = Interval(3, 4)
        self.assertEqual(-i, Interval(-4, -3))

    def test_math_functions(self):
        # Simply show that we can call the functions.
        i1 = Interval(0.1, 0.3)
        i2 = Interval(0.2, 0.4)
        print(sqr(i1))
        print(sqrt(i1))
        print(pow(i1, 2))
        print(pow(i1, 2.5))
        print(pow(i1, Interval(1, 2)))
        print(root(i1, 2))
        print(exp(i1))
        print(log(i1))
        print(cos(i1))
        print(tan(i1))
        print(sin(i1))
        print(acos(i1))
        print(asin(i1))
        print(atan(i1))
        print(atan2(i1, i2))
        print(cosh(i1))
        print(sinh(i1))
        print(tanh(i1))
        print(abs(i1))
        print(max(i1, i2))
        print(min(i1, i2))
        print(sign(i1))
        print(integer(i1))

    def test_eq_neq(self):
        i1 = Interval(3, 4)
        i2 = Interval(3, 5)
        i3 = Interval(3, 4)
        self.assertNotEqual(i1, i2)
        self.assertEqual(i1, i3)

    def test_empty(self):
        i = Interval(3, 4)
        self.assertFalse(i.is_empty())
        i.set_empty()
        self.assertTrue(i.is_empty())

    def test_to_string(self):
        i = Interval(3, 4)
        self.assertEqual(str(i), "[3, 4]")
        self.assertEqual(repr(i), "Interval(3, 4)")

    def test_intersection(self):
        i1 = Interval(2, 5)
        i2 = Interval(3, 8)
        self.assertEqual(i1 & i2, Interval(3, 5))
        i2 &= i1
        self.assertEqual(i2, Interval(3, 5))

    def test_union(self):
        i1 = Interval(2, 5)
        i2 = Interval(3, 8)
        self.assertEqual(i1 | i2, Interval(2, 8))
        i2 |= i1
        self.assertEqual(i2, Interval(2, 8))

    def test_inflate(self):
        i = Interval(2, 5)
        i.inflate(1)
        self.assertEqual(i, Interval(1, 6))
        i.inflate(2, 3)
        self.assertEqual(i, Interval(-4.5, 11.5))

    def test_mid_rad_diam(self):
        i = Interval(0, 1)
        self.assertEqual(i.mid(), 0.5)
        self.assertEqual(i.rad(), 0.5)
        self.assertEqual(i.diam(), 0.5 * 2)

    def test_mig_mag(self):
        i = Interval(2, 3)
        self.assertEqual(i.mig(), 2)
        self.assertEqual(i.mag(), 3)

    def test_contains(self):
        i = Interval(2, 3)
        self.assertTrue(i.contains(2.5))
        self.assertTrue(i.interior_contains(2.5))
        self.assertTrue(2.5 in i)
        self.assertFalse(i.contains(3.5))
        self.assertFalse(3.5 in i)
        self.assertFalse(i.interior_contains(2))

    def test_inclusions(self):
        i1 = Interval(2, 3)
        i2 = Interval(4, 5)
        i3 = Interval(1, 6)
        i4 = Interval(2, 4)

        self.assertTrue(i1.is_subset(i3))
        self.assertFalse(i1.is_strict_subset(i1))
        self.assertFalse(i1.is_interior_subset(i4))
        self.assertFalse(i1.is_relative_interior_subset(i4))
        self.assertFalse(i1.is_strict_interior_subset(i2))
        self.assertTrue(i3.is_superset(i1))
        self.assertTrue(i3.is_strict_superset(i1))

        self.assertTrue(i1.intersects(i4))
        self.assertTrue(i1.overlaps(i4))
        self.assertTrue(i1.is_disjoint(i2))

        self.assertFalse(i1.is_degenerated())
        self.assertFalse(i1.is_unbounded())
        self.assertTrue(i1.is_bisectable())

    def test_distance(self):
        i1 = Interval(2, 3)
        i2 = Interval(4, 5)
        self.assertEqual(i1.rel_distance(i2), 2)

    def test_complementary(self):
        i1 = Interval()
        i2 = Interval()
        Interval(2, 3).complementary(i1, i2, True)
        self.assertEqual(i1, Interval(-inf, 2))
        self.assertEqual(i2, Interval(3, inf))

    def test_diff(self):
        i1 = Interval()
        i2 = Interval()
        Interval(1, 10).diff(Interval(2, 5), i1, i2, True)
        self.assertEqual(i1, Interval(1, 2))
        self.assertEqual(i2, Interval(5, 10))

    def test_div2(self):
        i = Interval(-10, 10)
        out = Interval()
        result = i.div2_inter(Interval(2, 3), Interval(-1, 2), out)
        self.assertEqual(result, True)
        self.assertEqual(i, Interval(-10, -2))
        self.assertEqual(out, Interval(1, 10))

    def test_bisect(self):
        (i1, i2) = Interval(-10, 10).bisect(0.5)
        self.assertEqual(i1, Interval(-10, 0))
        self.assertEqual(i2, Interval(0, 10))

    def test_static_constants(self):
        self.assertAlmostEqual(Interval.PI.lb(), math.pi)
        self.assertAlmostEqual(Interval.PI.ub(), math.pi)
        self.assertAlmostEqual(Interval.TWO_PI.lb(), 2 * math.pi)
        self.assertAlmostEqual(Interval.TWO_PI.ub(), 2 * math.pi)
        self.assertAlmostEqual(Interval.HALF_PI.lb(), math.pi / 2)
        self.assertAlmostEqual(Interval.HALF_PI.ub(), math.pi / 2)
        self.assertTrue(Interval.EMPTY_SET.is_empty())
        self.assertAlmostEqual(Interval.ALL_REALS.lb(), -inf)
        self.assertAlmostEqual(Interval.ALL_REALS.ub(), +inf)
        self.assertAlmostEqual(Interval.ZERO.lb(), 0)
        self.assertAlmostEqual(Interval.ZERO.ub(), 0)
        self.assertAlmostEqual(Interval.ONE.lb(), 1)
        self.assertAlmostEqual(Interval.ONE.ub(), 1)
        self.assertAlmostEqual(Interval.POS_REALS.lb(), 0)
        self.assertAlmostEqual(Interval.POS_REALS.ub(), inf)
        self.assertAlmostEqual(Interval.NEG_REALS.lb(), -inf)
        self.assertAlmostEqual(Interval.NEG_REALS.ub(), 0)


class BoxTest(unittest.TestCase):
    def test_copy_constructor(self):
        b1 = Box([x, y, z])
        b2 = Box([x, y, z])
        self.assertEqual(b1, b2)
        b2.set_empty()
        self.assertNotEqual(b1, b2)

    def test_size_empty_set_empty(self):
        b = Box([x, y, z])
        self.assertEqual(b.size(), 3)
        self.assertFalse(b.empty())
        b.set_empty()
        self.assertTrue(b.empty())

    def test_string(self):
        b = Box([x])
        self.assertEqual(str(b), "x : [ ENTIRE ]")
        self.assertEqual(repr(b), '<Box "x : [ ENTIRE ]">')

    def test_get_set_item_variable(self):
        b = Box([x, y, z])
        b[x] = Interval(3, 4)
        self.assertEqual(b[x], Interval(3, 4))

    def test_get_set_item_int(self):
        b = Box([x, y, z])
        self.assertEqual(b.variable(0), x)
        b[0] = Interval(3, 4)
        self.assertEqual(b[0], Interval(3, 4))

    def test_index(self):
        b = Box([x, y, z])
        self.assertEqual(b.index(x), 0)

    def test_bisect_int(self):
        b = Box([x, y, z])
        (b1, b2) = b.bisect(0)
        self.assertEqual(b1[0].ub(), 0)
        self.assertEqual(b2[0].lb(), 0)

    def test_bisect_variable(self):
        b = Box([x, y, z])
        (b1, b2) = b.bisect(x)
        self.assertEqual(b1[x].ub(), 0)
        self.assertEqual(b2[x].lb(), 0)

    def test_max_diam(self):
        b = Box([x, y])
        b[x] = Interval(0.1, 0.2)
        b[y] = Interval(1, 2)
        (diam, idx) = b.MaxDiam()
        self.assertEqual(idx, 1)
        self.assertEqual(b[idx].diam(), 1)

    def test_inplace_union(self):
        b1 = Box([x, y])
        b1[x] = Interval(1, 3)
        b1[y] = Interval(1, 2)

        b2 = Box([x, y])
        b2[x] = Interval(2, 4)
        b2[y] = Interval(3, 5)

        b2.InplaceUnion(b1)
        self.assertEqual(b2[x], Interval(1, 4))
        self.assertEqual(b2[y], Interval(1, 5))

    def test_add(self):
        b = Box([x])
        b.Add(y)
        b.Add(z, 2, 5)
        self.assertEqual(b[y], Interval())
        self.assertEqual(b[z], Interval(2, 5))

    def test_keys_values_items(self):
        b = Box([x])
        b.Add(y)
        b.Add(z, 2, 5)
        self.assertEqual(b.keys(), [x, y, z])
        self.assertEqual(
            b.values(),
            [Interval(-inf, inf),
             Interval(-inf, inf),
             Interval(2, 5)])
        self.assertEqual(b.items(), [(x, Interval(-inf, inf)),
                                     (y, Interval(-inf, inf)),
                                     (z, Interval(2, 5))])

    def to_dictionary(self):
        b = Box([x])
        b.Add(y)
        b.Add(z, 2, 5)
        d = dict(b)
        self.assertEqual(d[y], Interval())
        self.assertEqual(d[z], Interval(2, 5))


if __name__ == '__main__':
    unittest.main()
