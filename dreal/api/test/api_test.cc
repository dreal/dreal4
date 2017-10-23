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
};

::testing::AssertionResult CheckSolution(const Formula& f,
                                         const Box& solution) {
  FormulaEvaluator formula_evaluator{
      make_relational_formula_evaluator(f, solution.variables())};
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
  const Variable b1{"b1", Variable::Type::BOOLEAN};
  const Variable b2{"b2", Variable::Type::BOOLEAN};
  const auto result = CheckSatisfiability(
      !b1 && b2 && (sin(x_) == 1) && x_ > 0 && x_ < 2 * 3.141592, 0.001);
  ASSERT_TRUE(result);
  EXPECT_EQ((*result)[b1], 0.0);
  EXPECT_EQ((*result)[b2], 1.0);
  EXPECT_NEAR(std::sin((*result)[x_].mid()), 1.0, 0.001);
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
  // minimize 2x² + 6x + 5 s.t. -4 ≤ x ≤ 0
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

}  // namespace
}  // namespace dreal
