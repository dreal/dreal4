#include "dreal/symbolic/symbolic.h"

#include <iostream>
#include <type_traits>

#include <gtest/gtest.h>

#include "dreal/symbolic/symbolic_test_util.h"

using std::cout;
using std::endl;

namespace dreal {
namespace {

class FormulaHelper : public ::testing::Test {
 protected:
  const Variable b1_{"B1", Variable::Type::BOOLEAN};
  const Variable b2_{"B2", Variable::Type::BOOLEAN};
  const Variable b3_{"B3", Variable::Type::BOOLEAN};
};

TEST_F(FormulaHelper, Imply) {
  // b₁ ⇒ b₂
  const Formula f{imply(Formula{b1_}, Formula{b2_})};

  // T ⇒ T  =  T
  EXPECT_PRED2(
      FormulaEqual,
      f.Substitute(b1_, Formula::True()).Substitute(b2_, Formula::True()),
      Formula::True());
  // T ⇒ F  =  F
  EXPECT_PRED2(
      FormulaEqual,
      f.Substitute(b1_, Formula::True()).Substitute(b2_, Formula::False()),
      Formula::False());
  // F ⇒ T  =  T
  EXPECT_PRED2(
      FormulaEqual,
      f.Substitute(b1_, Formula::False()).Substitute(b2_, Formula::True()),
      Formula::True());
  // F ⇒ F  =  T
  EXPECT_PRED2(
      FormulaEqual,
      f.Substitute(b1_, Formula::False()).Substitute(b2_, Formula::False()),
      Formula::True());
}

TEST_F(FormulaHelper, Iff) {
  // b₁ ⇔ b₂
  const Formula f{iff(Formula{b1_}, Formula{b2_})};

  // T ⇔ T  =  T
  EXPECT_PRED2(
      FormulaEqual,
      f.Substitute(b1_, Formula::True()).Substitute(b2_, Formula::True()),
      Formula::True());
  // T ⇔ F  =  F
  EXPECT_PRED2(
      FormulaEqual,
      f.Substitute(b1_, Formula::True()).Substitute(b2_, Formula::False()),
      Formula::False());
  // F ⇔ T  =  F
  EXPECT_PRED2(
      FormulaEqual,
      f.Substitute(b1_, Formula::False()).Substitute(b2_, Formula::True()),
      Formula::False());
  // F ⇔ F  =  T
  EXPECT_PRED2(
      FormulaEqual,
      f.Substitute(b1_, Formula::False()).Substitute(b2_, Formula::False()),
      Formula::True());
}

GTEST_TEST(Symbolic, is_nothrow_move_constructible) {
  static_assert(std::is_nothrow_move_constructible<Variable>::value,
                "Variable should be nothrow_move_constructible.");
  static_assert(std::is_nothrow_move_constructible<Expression>::value,
                "Expression should be nothrow_move_constructible.");
  static_assert(std::is_nothrow_move_constructible<Formula>::value,
                "Formula should be nothrow_move_constructible.");
}

}  // namespace
}  // namespace dreal
