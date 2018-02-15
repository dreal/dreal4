#include "dreal/util/if_then_else_eliminator.h"

#include <vector>

#include <gtest/gtest.h>

#include "dreal/api/api.h"
#include "dreal/symbolic/symbolic_test_util.h"

namespace dreal {
namespace {

using std::vector;

class IfThenElseEliminatorTest : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};

  const Variable b1_{"b1", Variable::Type::BOOLEAN};
  const Variable b2_{"b1", Variable::Type::BOOLEAN};

  // The following formulas do not include if-then-else expressions
  // and as a result should not be changed in the process of ite-elim.
  const vector<Formula> non_ites_{
      // clang-format off
      Formula::True(),
      Formula::False(),
      // Relational operators
      x_ + y_ == z_,
      x_ + y_ != z_,
      x_ + y_ > z_,
      x_ + y_ >= z_,
      x_ + y_ < z_,
      x_ + y_ <= z_,
      // Constant
      y_ == 4,
      // Addition, multiplication, division
      1 + x_ + y_ * 3 / z_ == 0,
      // math functions
      log(x_) == abs(y_),
      exp(x_) > sqrt(y_),
      pow(x_, y_) < sin(z_),
      cos(x_) >= tan(y_),
      asin(x_) <= acos(y_),
      atan(x_) >= atan2(y_, z_),
      sinh(x_) == cosh(y_),
      tanh(x_) == min(y_, z_),
      max(x_, y_) != z_,
      !b1_,
      uninterpreted_function("uf", {x_, y_, z_}) == 0.0,
      (b1_ && b2_) || (!b1_ && !b2_),
      // clang-format on
  };
};

TEST_F(IfThenElseEliminatorTest, NonITEs) {
  for (const Formula& f : non_ites_) {
    IfThenElseEliminator ite_elim;
    EXPECT_PRED2(FormulaEqual, f, ite_elim.Process(f));
  }
}

TEST_F(IfThenElseEliminatorTest, NonITEsInForall) {
  for (const Formula& f : non_ites_) {
    IfThenElseEliminator ite_elim;
    const Formula forall_f{forall({x_}, f)};
    EXPECT_PRED2(FormulaEqual, forall_f, ite_elim.Process(forall_f));
  }
}

TEST_F(IfThenElseEliminatorTest, ITEs) {
  const Formula f{if_then_else(x_ > y_, x_ + 1.0, y_ + 1.0) == z_};
  IfThenElseEliminator ite_elim;
  const Formula converted = ite_elim.Process(f);
  ASSERT_FALSE(ite_elim.variables().empty());
  ASSERT_EQ(ite_elim.variables().size(), 1);
  const Variable& ite_var{*(ite_elim.variables().begin())};
  const Formula expected{ite_var == z_ && imply(x_ > y_, ite_var == x_ + 1.0) &&
                         imply(!(x_ > y_), ite_var == y_ + 1.0)};
  EXPECT_PRED2(FormulaNotEqual, f, converted);
  EXPECT_PRED2(FormulaEqual, converted, expected);
}

}  // namespace
}  // namespace dreal
