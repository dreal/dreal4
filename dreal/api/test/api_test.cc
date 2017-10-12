#include "dreal/api/api.h"

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

TEST_F(ApiTest, CheckSatisfiability1) {
  // 0 ≤ x ≤ 5
  // 0 ≤ y ≤ 5
  // 0 ≤ z ≤ 5
  // 2x + y = z
  const Formula f1{0 <= x_ && x_ <= 5};
  const Formula f2{0 <= y_ && y_ <= 5};
  const Formula f3{0 <= z_ && z_ <= 5};
  const Formula f4{2 * x_ + y_ == z_};

  auto result = CheckSatisfiability(f1 && f2 && f3 && f4, 0.001);
  ASSERT_TRUE(result);

  const Box& solution{*result};
  FormulaEvaluator formula_evaluator{
      make_relational_formula_evaluator(f4, solution.variables())};
  const FormulaEvaluationResult formula_evaluation_result{
      formula_evaluator(solution)};
  EXPECT_TRUE(formula_evaluation_result.type() !=
              FormulaEvaluationResult::Type::UNSAT);
  // This indicates that `2 * x + y == z` is true with the found solution.
  EXPECT_TRUE(formula_evaluation_result.evaluation().contains(0.0));
}

TEST_F(ApiTest, CheckSatisfiability2) {
  // 2x² + 6x + 5 < 0
  // -10 ≤ x ≤ 10
  const Formula f1{2 * x_ * x_ + 6 * x_ + 5 < 0};
  const Formula f2{-10 <= x_ && x_ <= 10};

  auto result = CheckSatisfiability(f1 && f2, 0.001);
  EXPECT_FALSE(result);
}

TEST_F(ApiTest, Minimize1) {
  // minimize 2x² + 6x + 5 s.t. -4 ≤ x ≤ 0
  const Expression objective{2 * x_ * x_ + 6 * x_ + 5};
  const Formula constraint{-10 <= x_ && x_ <= 10};

  const double delta{0.01};
  auto result = Minimize(objective, constraint, delta);
  ASSERT_TRUE(result);
  const double x = (*result)[x_].mid();
  const double known_minimum = 0.5;
  EXPECT_TRUE(-10 <= x && x <= 10);
  EXPECT_LT(2 * x * x + 6 * x + 5, known_minimum + delta);
}

TEST_F(ApiTest, Minimize2) {
  // minimize sin(3x) - 2cos(x) s.t. -3 ≤ x ≤ 3
  const Expression objective{sin(3 * x_) - 2 * cos(x_)};
  const Formula constraint{-3 <= x_ && x_ <= 3};

  const double delta{0.001};
  auto result = Minimize(objective, constraint, delta);
  ASSERT_TRUE(result);
  const double x = (*result)[x_].mid();
  const double known_minimum = -2.77877;
  EXPECT_TRUE(-3 <= x && x <= 3);
  EXPECT_LT(sin(3 * x) - 2 * cos(x), known_minimum + delta);
}

}  // namespace
}  // namespace dreal
