/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
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
