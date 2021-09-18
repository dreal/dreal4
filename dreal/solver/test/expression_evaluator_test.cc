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
#include "dreal/solver/expression_evaluator.h"

#include <iostream>
#include <sstream>

#include <gtest/gtest.h>

namespace dreal {
namespace {

using std::cerr;
using std::endl;
using std::ostringstream;

class ExpressionEvaluatorTest : public ::testing::Test {
 protected:
  void SetUp() override {
    box_.Add(x_);
    box_.Add(y_);
    box_.Add(z_);
  }

  const Variable x_{"x"};
  const Variable y_{"y"};
  const Variable z_{"z"};
  Box box_;
};

TEST_F(ExpressionEvaluatorTest, Arithmetic1) {
  const Expression e{x_ + y_ + z_};
  const ExpressionEvaluator evaluator{e};

  box_[x_] = Box::Interval{1, 2};
  box_[y_] = Box::Interval{2, 3};
  box_[z_] = Box::Interval{3, 4};

  EXPECT_EQ(evaluator(box_), Box::Interval(1 + 2 + 3, 2 + 3 + 4));
  ostringstream oss;
  oss << evaluator;
  EXPECT_EQ(oss.str(), "ExpressionEvaluator((x + y + z))");
}

// TODO(soonho): Add more tests.

}  // namespace
}  // namespace dreal
