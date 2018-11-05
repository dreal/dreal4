#include "dreal/util/math.h"

#include <limits>
#include <stdexcept>

#include <gtest/gtest.h>

namespace dreal {
namespace {

using std::numeric_limits;
using std::runtime_error;

GTEST_TEST(MathTest, is_integer) {
  EXPECT_TRUE(is_integer(3.0));
  EXPECT_FALSE(is_integer(3.1));
}

GTEST_TEST(MathTest, convert_long_to_int) {
  EXPECT_EQ(convert_long_to_int(3017294l), 3017294);
  EXPECT_THROW(convert_long_to_int(numeric_limits<int>::max() + 1l),
               runtime_error);
  EXPECT_THROW(convert_long_to_int(numeric_limits<int>::min() - 1l),
               runtime_error);
}

GTEST_TEST(MathTest, convert_long_to_double) {
  EXPECT_EQ(convert_long_to_double(3017294l), 3017294.0);

  // NOLINTNEXTLINE(runtime/int)
  constexpr long m1{1l << numeric_limits<double>::digits};
  constexpr double m2{1l << numeric_limits<double>::digits};

  EXPECT_EQ(convert_long_to_double(m1), m2);
  EXPECT_THROW(convert_long_to_double(m1 + 1), runtime_error);
  EXPECT_THROW(convert_long_to_double(-m1 - 1), runtime_error);
}

}  // namespace
}  // namespace dreal
