#include "dreal/util/string_to_interval.h"

#include <gtest/gtest.h>

namespace dreal {
namespace {

GTEST_TEST(StringToIntervalTest, InexactPositive) {
  const Box::Interval i{StringToInterval("0.1")};
  EXPECT_FALSE(i.is_empty());
  EXPECT_LT(0, i.diam());
  EXPECT_LE(i.lb(), 0.1);
  EXPECT_GE(i.ub(), 0.1);
}

GTEST_TEST(StringToIntervalTest, InexactNegative) {
  const Box::Interval i{StringToInterval("-0.1")};
  EXPECT_FALSE(i.is_empty());
  EXPECT_LT(0, i.diam());
  EXPECT_LE(i.lb(), -0.1);
  EXPECT_GE(i.ub(), -0.1);
}

GTEST_TEST(StringToIntervalTest, ExactPositive) {
  const Box::Interval i{StringToInterval("0.5")};
  EXPECT_FALSE(i.is_empty());
  EXPECT_EQ(0, i.diam());
  EXPECT_EQ(i.lb(), 0.5);
  EXPECT_EQ(i.ub(), 0.5);
}

GTEST_TEST(StringToIntervalTest, ExactNegative) {
  const Box::Interval i{StringToInterval("-0.5")};
  EXPECT_FALSE(i.is_empty());
  EXPECT_EQ(0, i.diam());
  EXPECT_EQ(i.lb(), -0.5);
  EXPECT_EQ(i.ub(), -0.5);
}

}  // namespace
}  // namespace dreal
