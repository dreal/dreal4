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
  const ExpressionEvaluator evaluator{e, box_};

  box_[x_] = Box::Interval{1, 2};
  box_[y_] = Box::Interval{2, 3};
  box_[z_] = Box::Interval{3, 4};

  EXPECT_EQ(evaluator(box_), Box::Interval(1 + 2 + 3, 2 + 3 + 4));
  EXPECT_EQ(evaluator.EvaluateAtCenter(box_),
            (1 + 2) / 2.0 + (2 + 3) / 2.0 + (3 + 4) / 2.0);
  ostringstream oss;
  oss << evaluator;
  EXPECT_EQ(oss.str(), "ExpressionEvaluator(_f_0:(x,y,z)->((x+y)+z))");
}

// TODO(soonho): Add more tests.

}  // namespace
}  // namespace dreal
