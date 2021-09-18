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
#include "dreal/util/math.h"

#include <limits>
#include <stdexcept>

#include <gtest/gtest.h>

namespace dreal {
namespace {

using std::int64_t;
using std::numeric_limits;
using std::runtime_error;

GTEST_TEST(MathTest, IsInteger) {
  EXPECT_TRUE(is_integer(3.0));
  EXPECT_FALSE(is_integer(3.1));
}

GTEST_TEST(MathTest, ConvertInt64ToInt) {
  EXPECT_EQ(convert_int64_to_int(3017294L), 3017294);
  EXPECT_THROW(convert_int64_to_int(numeric_limits<int>::max() + 1L),
               runtime_error);
  EXPECT_THROW(convert_int64_to_int(numeric_limits<int>::min() - 1L),
               runtime_error);
}

GTEST_TEST(MathTest, ConvertInt64ToDouble) {
  EXPECT_EQ(convert_int64_to_double(3017294L), 3017294.0);
  constexpr int64_t m1{1UL << numeric_limits<double>::digits};
  constexpr double m2{1UL << numeric_limits<double>::digits};

  EXPECT_EQ(convert_int64_to_double(m1), m2);
  EXPECT_THROW(convert_int64_to_double(m1 + 1), runtime_error);
  EXPECT_THROW(convert_int64_to_double(-m1 - 1), runtime_error);
}

}  // namespace
}  // namespace dreal
