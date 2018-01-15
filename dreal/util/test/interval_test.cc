#include "dreal/util/interval.h"

#include <limits>

#include <gtest/gtest.h>

namespace dreal {

using std::numeric_limits;

GTEST_TEST(IntervalTest, BloatPoint) {
  const double c1{3.14159265339999960176};
  const double c2{3.1415926534};
  const double c3{3.141592653400000489938};
  EXPECT_LT(c1, c2);
  EXPECT_LT(c2, c3);

  const Box::Interval bloated{BloatPoint(c2)};
  EXPECT_EQ(bloated.lb(), c1);
  EXPECT_EQ(bloated.ub(), c3);
}

GTEST_TEST(IntervalTest, BloatPointPosInf) {
  const double inf{numeric_limits<double>::infinity()};
  const double max{numeric_limits<double>::max()};

  const Box::Interval bloated{BloatPoint(inf)};
  EXPECT_EQ(bloated.lb(), max);
  EXPECT_EQ(bloated.ub(), inf);
}

GTEST_TEST(IntervalTest, BloatPointNegInf) {
  const double inf{numeric_limits<double>::infinity()};
  const double max{numeric_limits<double>::max()};

  const Box::Interval bloated{BloatPoint(-inf)};
  EXPECT_EQ(bloated.lb(), -inf);
  EXPECT_EQ(bloated.ub(), -max);
}

}  // namespace dreal
