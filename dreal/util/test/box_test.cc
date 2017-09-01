#include "dreal/util/box.h"

#include <iostream>
#include <limits>
#include <type_traits>
#include <vector>

#include <gtest/gtest.h>

#include "dreal/symbolic/symbolic.h"

using std::cout;
using std::endl;
using std::numeric_limits;
using std::vector;

namespace dreal {
// TODO(soonho): Add more tests.
namespace {

GTEST_TEST(BoxTest, InplaceUnion) {
  const Variable x{"x"};
  const Variable y{"y"};

  Box b1{{x, y}};
  b1[x] = Box::Interval(0, 1);
  b1[y] = Box::Interval(0, 1);

  Box b2{{x, y}};
  b2[x] = Box::Interval(2, 3);
  b2[y] = Box::Interval(3, 4);

  b1.InplaceUnion(b2);
  EXPECT_EQ(b1[x], Box::Interval(0, 3));
  EXPECT_EQ(b1[y], Box::Interval(0, 4));

  // No changes on b2.
  EXPECT_EQ(b2[x], Box::Interval(2, 3));
  EXPECT_EQ(b2[y], Box::Interval(3, 4));
}

GTEST_TEST(BoxTest, BisectInt) {
  const Variable x{"x", Variable::Type::INTEGER};
  const Variable y{"y", Variable::Type::INTEGER};
  Box b;
  b.Add(x);
  b.Add(y);
  b[x] = Box::Interval(-numeric_limits<double>::infinity(),
                       numeric_limits<double>::infinity());
  b[y] = Box::Interval(-numeric_limits<double>::infinity(),
                       numeric_limits<double>::infinity());
  const std::pair<Box, Box> p{b.bisect(x)};
  EXPECT_FALSE(p.first.empty());
  EXPECT_FALSE(p.second.empty());
}

GTEST_TEST(BoxTest, is_nothrow_move_constructible) {
  static_assert(std::is_nothrow_move_constructible<Box::Interval>::value,
                "Box::Interval should be nothrow_move_constructible.");
  static_assert(std::is_nothrow_move_constructible<Box::IntervalVector>::value,
                "Box::IntervalVector should be nothrow_move_constructible.");
  static_assert(std::is_nothrow_move_constructible<Box>::value,
                "Box should be nothrow_move_constructible.");
}

}  // namespace
}  // namespace dreal
