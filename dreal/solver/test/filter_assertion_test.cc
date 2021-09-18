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
#include "dreal/solver/filter_assertion.h"

#include <gtest/gtest.h>

#include "dreal/symbolic/symbolic.h"

namespace dreal {
namespace {

class FilterAssertionTest : public ::testing::Test {
 protected:
  void SetUp() override { box_[z_] = Box::Interval(-100, 100); }
  const Variable z_{"z"};
  const Variable x_{"x"};
  Box box_{{{z_}}};
};

TEST_F(FilterAssertionTest, FilteredWithChange1) {
  // (z < 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(z_ < 50, &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_LT(box_[z_].ub(), 50);
  // No change on z.lb().
  EXPECT_EQ(box_[z_].lb(), old_box[z_].lb());
}

TEST_F(FilterAssertionTest, FilteredWithChange2) {
  // ¬(z < 50) => (z >= 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(!(z_ < 50), &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_EQ(box_[z_].lb(), 50);
  // No change on z.ub().
  EXPECT_EQ(box_[z_].ub(), old_box[z_].ub());
}

TEST_F(FilterAssertionTest, FilteredWithChange3) {
  // (z <= 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(z_ <= 50, &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_LE(box_[z_].ub(), 50);
  // No change on z.lb().
  EXPECT_EQ(box_[z_].lb(), old_box[z_].lb());
}

TEST_F(FilterAssertionTest, FilteredWithChange4) {
  // ¬(z <= 50) => (z > 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(!(z_ <= 50), &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_GT(box_[z_].lb(), 50);
  // No change on z.ub().
  EXPECT_EQ(box_[z_].ub(), old_box[z_].ub());
}

TEST_F(FilterAssertionTest, FilteredWithChange5) {
  // (z > 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(z_ > 50, &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_GT(box_[z_].lb(), 50);
  // No change on z.ub().
  EXPECT_EQ(box_[z_].ub(), old_box[z_].ub());
}

TEST_F(FilterAssertionTest, FilteredWithChange6) {
  // ¬(z > 50) => (z <= 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(!(z_ > 50), &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_LE(box_[z_].ub(), 50);
  // No change on z.lb().
  EXPECT_EQ(box_[z_].lb(), old_box[z_].lb());
}

TEST_F(FilterAssertionTest, FilteredWithChange7) {
  // (z >= 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(z_ >= 50, &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_GE(box_[z_].lb(), 50);
  // No change on z.ub().
  EXPECT_EQ(box_[z_].ub(), old_box[z_].ub());
}

TEST_F(FilterAssertionTest, FilteredWithChange8) {
  // ¬(z >= 50) => (z < 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(!(z_ >= 50), &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_LT(box_[z_].ub(), 50);
  // No change on z.lb().
  EXPECT_EQ(box_[z_].lb(), old_box[z_].lb());
}

TEST_F(FilterAssertionTest, FilteredWithChange9) {
  // (z == 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(z_ == 50, &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_EQ(box_[z_].lb(), 50);
  EXPECT_EQ(box_[z_].ub(), 50);
}

TEST_F(FilterAssertionTest, NotFiltered1) {
  // ¬(z == 50) => (z != 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(!(z_ == 50), &box_);
  EXPECT_EQ(result, FilterAssertionResult::NotFiltered);
  EXPECT_EQ(box_, old_box);
}

TEST_F(FilterAssertionTest, NotFiltered2) {
  // (z != 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(z_ != 50, &box_);
  EXPECT_EQ(result, FilterAssertionResult::NotFiltered);
  EXPECT_EQ(box_, old_box);
}

TEST_F(FilterAssertionTest, FilteredWithChange10) {
  // ¬(z != 50) => (z == 50)
  const Box old_box{box_};
  const auto result = FilterAssertion(!(z_ != 50), &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_EQ(box_[z_].lb(), 50);
  EXPECT_EQ(box_[z_].ub(), 50);
}

TEST_F(FilterAssertionTest, FilteredWithoutChange1) {
  // (z < 150)
  const Box old_box{box_};
  const auto result = FilterAssertion(z_ < 150, &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithoutChange);
  EXPECT_EQ(old_box, box_);
}

TEST_F(FilterAssertionTest, Empty1) {
  // !(z < 150) => (z >= 150) => Empty box
  const Box old_box{box_};
  const auto result = FilterAssertion(!(z_ < 150), &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_TRUE(box_.empty());
}

TEST_F(FilterAssertionTest, FilteredWithoutChange2) {
  // (z <= 150)
  const Box old_box{box_};
  const auto result = FilterAssertion(z_ <= 150, &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithoutChange);
  EXPECT_EQ(old_box, box_);
}

TEST_F(FilterAssertionTest, Empty2) {
  // !(z < 150) => (z >= 150) => Empty box
  const Box old_box{box_};
  const auto result = FilterAssertion(!(z_ <= 150), &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_TRUE(box_.empty());
}

TEST_F(FilterAssertionTest, FilteredWithoutChange3) {
  // (z > -150)
  const Box old_box{box_};
  const auto result = FilterAssertion(z_ > -150, &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithoutChange);
  EXPECT_EQ(old_box, box_);
}

TEST_F(FilterAssertionTest, Empty3) {
  // !(z > -150) => (z <= -150) => Empty box
  const Box old_box{box_};
  const auto result = FilterAssertion(!(z_ > -150), &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_TRUE(box_.empty());
}

TEST_F(FilterAssertionTest, FilteredWithoutChange4) {
  // (z >= -150)
  const Box old_box{box_};
  const auto result = FilterAssertion(z_ >= -150, &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithoutChange);
  EXPECT_EQ(old_box, box_);
}

TEST_F(FilterAssertionTest, Empty4) {
  // !(z >= -150) => (z < -150) => Empty box
  const Box old_box{box_};
  const auto result = FilterAssertion(!(z_ >= -150), &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_TRUE(box_.empty());
}

TEST_F(FilterAssertionTest, Equality1) {
  box_[z_] = 1.0;
  const Box old_box{box_};
  // z == 1.0
  const auto result = FilterAssertion(z_ == 1.0, &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithoutChange);
  EXPECT_EQ(old_box, box_);
}

TEST_F(FilterAssertionTest, Empty5) {
  const Box old_box{box_};
  // z == 150
  const auto result = FilterAssertion(z_ == 150, &box_);
  EXPECT_EQ(result, FilterAssertionResult::FilteredWithChange);
  EXPECT_TRUE(box_.empty());
}

TEST_F(FilterAssertionTest, NotFiltered) {
  const Box old_box{box_};
  const auto result = FilterAssertion(z_ == x_, &box_);
  EXPECT_EQ(result, FilterAssertionResult::NotFiltered);
  EXPECT_EQ(old_box, box_);
}

}  // namespace
}  // namespace dreal
