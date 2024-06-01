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
#include "dreal/api/api.h"

#include <cmath>

#include <gtest/gtest.h>

#include "dreal/solver/formula_evaluator.h"

namespace dreal {
namespace {

class ApiTest : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};

  const Variable binary1_{"binary1", Variable::Type::BINARY};
  const Variable binary2_{"binary2", Variable::Type::BINARY};

  const Variable b1_{"b1", Variable::Type::BOOLEAN};
  const Variable b2_{"b2", Variable::Type::BOOLEAN};
};

::testing::AssertionResult CheckSolution(const Formula& f,
                                         const Box& solution) {
  FormulaEvaluator formula_evaluator{make_relational_formula_evaluator(f)};
  const FormulaEvaluationResult formula_evaluation_result{
      formula_evaluator(solution)};
  if (formula_evaluation_result.type() ==
      FormulaEvaluationResult::Type::UNSAT) {
    return ::testing::AssertionFailure() << "UNSAT detected!";
  }
  if (!formula_evaluation_result.evaluation().contains(0.0)) {
    return ::testing::AssertionFailure() << "The interval evaluation indicates "
                                            "that the solution does not "
                                            "satisfy the constraint.";
  }
  return ::testing::AssertionSuccess();
}

// Tests CheckSatisfiability (δ-SAT case).
TEST_F(ApiTest, CheckSatisfiabilityMixedBooleanAndContinuous) {
  const auto result = CheckSatisfiability(
      !b1_ && b2_ && (sin(x_) == 1) && x_ > 0 && x_ < 2 * 3.141592, 0.001);
  ASSERT_TRUE(result);
  EXPECT_EQ((*result)[b1_], 0.0);
  EXPECT_EQ((*result)[b2_], 1.0);
  EXPECT_NEAR(std::sin((*result)[x_].mid()), 1.0, 0.001);
}

TEST_F(ApiTest, CheckSatisfiabilityBinaryVariables1) {
  const Formula f{2 * binary1_ + 4 * binary2_ == 0};
  const auto result = CheckSatisfiability(f, 0.001);
  ASSERT_TRUE(result);
  const Box& solution{*result};
  EXPECT_EQ(solution[binary1_].mid(), 0.0);
  EXPECT_EQ(solution[binary2_].mid(), 0.0);
  EXPECT_EQ(solution[binary1_].diam(), 0.0);
  EXPECT_EQ(solution[binary2_].diam(), 0.0);
}

TEST_F(ApiTest, CheckSatisfiabilityBinaryVariables2) {
  const Formula f{binary1_ + binary2_ > 3};
  const auto result = CheckSatisfiability(f, 0.001);
  EXPECT_FALSE(result);
}

// Tests CheckSatisfiability (δ-SAT case).
TEST_F(ApiTest, CheckSatisfiabilityDeltaSat) {
  // 0 ≤ x ≤ 5
  // 0 ≤ y ≤ 5
  // 0 ≤ z ≤ 5
  // 2x + y = z
  const Formula f1{0 <= x_ && x_ <= 5};
  const Formula f2{0 <= y_ && y_ <= 5};
  const Formula f3{0 <= z_ && z_ <= 5};
  const Formula f4{2 * x_ + y_ == z_};

  // Checks the API returning an optional.
  {
    auto result = CheckSatisfiability(f1 && f2 && f3 && f4, 0.001);
    ASSERT_TRUE(result);
    EXPECT_TRUE(CheckSolution(f4, *result));
  }

  // Checks the API returning a bool.
  {
    Box b;
    const bool result{CheckSatisfiability(f1 && f2 && f3 && f4, 0.001, &b)};
    ASSERT_TRUE(result);
    EXPECT_TRUE(CheckSolution(f4, b));
  }
}

// Tests CheckSatisfiability (UNSAT case).
TEST_F(ApiTest, CheckSatisfiabilityUnsat) {
  // 2x² + 6x + 5 < 0
  // -10 ≤ x ≤ 10
  const Formula f1{2 * x_ * x_ + 6 * x_ + 5 < 0};
  const Formula f2{-10 <= x_ && x_ <= 10};

  // Checks the API returning an optional.
  {
    auto result = CheckSatisfiability(f1 && f2, 0.001);
    EXPECT_FALSE(result);
  }

  // Checks the API returning a bool.
  {
    Box b;
    const bool result{CheckSatisfiability(f1 && f2, 0.001, &b)};
    EXPECT_FALSE(result);
  }
}

TEST_F(ApiTest, Minimize1) {
  // minimize 2x² + 6x + 5 s.t. -10 ≤ x ≤ 10
  const Expression objective{2 * x_ * x_ + 6 * x_ + 5};
  const Formula constraint{-10 <= x_ && x_ <= 10};
  const double delta{0.01};
  const double known_minimum = 0.5;

  // Checks the API returning an optional.
  {
    const auto result = Minimize(objective, constraint, delta);
    ASSERT_TRUE(result);
    const double x = (*result)[x_].mid();
    EXPECT_TRUE(-10 <= x && x <= 10);
    EXPECT_LT(2 * x * x + 6 * x + 5, known_minimum + delta);
  }

  // Checks the API returning a bool.
  {
    Box b;
    const bool result = Minimize(objective, constraint, delta, &b);
    ASSERT_TRUE(result);
    const double x = b[x_].mid();
    EXPECT_TRUE(-10 <= x && x <= 10);
    EXPECT_LT(2 * x * x + 6 * x + 5, known_minimum + delta);
  }
}

TEST_F(ApiTest, Minimize2) {
  // minimize sin(3x) - 2cos(x) s.t. -3 ≤ x ≤ 3
  const Expression objective{sin(3 * x_) - 2 * cos(x_)};
  const Formula constraint{-3 <= x_ && x_ <= 3};
  const double delta{0.001};
  const double known_minimum = -2.77877;

  // Checks the API returning an optional.
  {
    const auto result = Minimize(objective, constraint, delta);
    ASSERT_TRUE(result);
    const double x = (*result)[x_].mid();
    EXPECT_TRUE(-3 <= x && x <= 3);
    EXPECT_LT(sin(3 * x) - 2 * cos(x), known_minimum + delta);
  }

  // Checks the API returning a bool.
  {
    Box b;
    const bool result = Minimize(objective, constraint, delta, &b);
    ASSERT_TRUE(result);
    const double x = b[x_].mid();
    EXPECT_TRUE(-3 <= x && x <= 3);
    EXPECT_LT(sin(3 * x) - 2 * cos(x), known_minimum + delta);
  }
}

TEST_F(ApiTest, CheckSatisfiabilityDisjunction) {
  const double delta{0.001};
  const Variable b1{"b1", Variable::Type::BOOLEAN};
  const Variable b2{"b2", Variable::Type::BOOLEAN};
  const Variable b3{"b3", Variable::Type::BOOLEAN};
  const auto result = CheckSatisfiability(b1 || !b2 || b3, delta);
  const Box& solution{*result};

  EXPECT_EQ(solution[b1].diam(), 0);
  EXPECT_EQ(solution[b2].diam(), 0);
  EXPECT_EQ(solution[b3].diam(), 0);

  const double v1{solution[b1].mid()};
  const double v2{solution[b2].mid()};
  const double v3{solution[b3].mid()};
  EXPECT_TRUE(v1 == 1.0 || v1 == 0.0);
  EXPECT_TRUE(v2 == 1.0 || v2 == 0.0);
  EXPECT_TRUE(v3 == 1.0 || v3 == 0.0);
  EXPECT_TRUE(v1 || !v2 || v3);
}

TEST_F(ApiTest, CheckSatisfiabilityIfThenElse1) {
  const double delta{0.001};
  const Formula f1{if_then_else(x_ > y_, x_, y_) == z_};
  const Formula f2{x_ == 100};
  const Formula f3{y_ == 50};
  const auto result = CheckSatisfiability(f1 && f2 && f3, delta);
  ASSERT_TRUE(result);
  const Box& solution{*result};
  EXPECT_EQ(solution[z_].mid(), 100);
  EXPECT_EQ(solution.size(), 3);
}

TEST_F(ApiTest, CheckSatisfiabilityIfThenElse2) {
  const double delta{0.001};
  const Formula f1{if_then_else(x_ > y_, x_, y_) == z_};
  const Formula f2{x_ == 50};
  const Formula f3{y_ == 100};
  const auto result = CheckSatisfiability(f1 && f2 && f3, delta);
  ASSERT_TRUE(result);
  const Box& solution{*result};
  EXPECT_EQ(solution[z_].mid(), 100);
  EXPECT_EQ(solution.size(), 3);
}

TEST_F(ApiTest, CheckSatisfiabilityForall) {
  Config config;
  config.mutable_use_local_optimization() = true;
  const Formula f{forall({y_}, x_ == y_)};
  const auto result = CheckSatisfiability(f, config);
  EXPECT_FALSE(result);
}

TEST_F(ApiTest, SatCheckDeterministicOutput) {
  const Formula f1{0 <= x_ && x_ <= 5};
  const Formula f2{0 <= y_ && y_ <= 5};
  const Formula f3{0 <= z_ && z_ <= 5};
  const Formula f4{2 * x_ + y_ == z_};

  const auto result1 = CheckSatisfiability(f1 && f2 && f3 && f4, 0.001);
  const auto result2 = CheckSatisfiability(f1 && f2 && f3 && f4, 0.001);
  ASSERT_TRUE(result1);
  ASSERT_TRUE(result2);
  EXPECT_EQ(*result1, *result2);
}

TEST_F(ApiTest, MinimizeCheckDeterministicOutput) {
  // Calling the same API twice and check that the outputs are identical.
  const Expression objective{2 * x_ * x_ + 6 * x_ + 5};
  const Formula constraint{-10 <= x_ && x_ <= 10};
  const double delta{0.01};

  const auto result1 = Minimize(objective, constraint, delta);
  const auto result2 = Minimize(objective, constraint, delta);
  ASSERT_TRUE(result1);
  ASSERT_TRUE(result2);
  ASSERT_EQ(*result1, *result2);
}

}  // namespace
}  // namespace dreal
