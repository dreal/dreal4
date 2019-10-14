#include "dreal/util/predicate_abstractor.h"

#include <iostream>
#include <set>

#include <gtest/gtest.h>

#include "dreal/symbolic/symbolic.h"
#include "dreal/symbolic/symbolic_test_util.h"

using std::set;

namespace dreal {
namespace {

class PredicateAbstractorTest : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};

  const Variable b1_{"b1", Variable::Type::BOOLEAN};
  const Variable b2_{"b2", Variable::Type::BOOLEAN};
  const Variable b3_{"b3", Variable::Type::BOOLEAN};

  PredicateAbstractor abstractor_;
};

TEST_F(PredicateAbstractorTest, False) {
  // False <-> False
  const Formula abstracted{abstractor_.Convert(Formula::False())};
  EXPECT_TRUE(is_false(abstracted));
}

TEST_F(PredicateAbstractorTest, True) {
  // True <-> True
  const Formula abstracted{abstractor_.Convert(Formula::True())};
  EXPECT_TRUE(is_true(abstracted));
}

TEST_F(PredicateAbstractorTest, Variable) {
  // b <-> b
  const Formula f{b1_};
  const Formula f_abstracted{abstractor_.Convert(f)};
  EXPECT_PRED2(FormulaEqual, f, f_abstracted);
}

TEST_F(PredicateAbstractorTest, Eq) {
  // x + y == 10 <-> b
  const Formula f{x_ + y_ == 10};
  const Formula f_abstracted{abstractor_.Convert(f)};

  EXPECT_FALSE(is_variable(f));
  ASSERT_TRUE(is_variable(f_abstracted));
  const Variable& var{get_variable(f_abstracted)};

  EXPECT_EQ(var.get_type(), Variable::Type::BOOLEAN);
  EXPECT_PRED2(FormulaEqual, abstractor_[var], f);
  EXPECT_PRED2(VarEqual, abstractor_[f], var);
}

TEST_F(PredicateAbstractorTest, Neq) {
  // x + y != 10 <-> !(x + y == 10)
  const Formula f{x_ + y_ != 10};
  const Formula f_abstracted{abstractor_.Convert(f)};

  EXPECT_FALSE(is_variable(f));
  ASSERT_TRUE(is_negation(f_abstracted));
  ASSERT_TRUE(is_variable(get_operand(f_abstracted)));
  const Variable& var{get_variable(get_operand(f_abstracted))};

  EXPECT_EQ(var.get_type(), Variable::Type::BOOLEAN);
  EXPECT_PRED2(FormulaEqual, abstractor_[var], x_ + y_ == 10);
  EXPECT_PRED2(VarEqual, abstractor_[x_ + y_ == 10], var);
}

TEST_F(PredicateAbstractorTest, Gt) {
  // x + y > 10 <-> !(x + y <= 10)
  const Formula f{x_ + y_ > 10};
  const Formula f_abstracted{abstractor_.Convert(f)};

  EXPECT_FALSE(is_variable(f));
  ASSERT_TRUE(is_negation(f_abstracted));
  ASSERT_TRUE(is_variable(get_operand(f_abstracted)));
  const Variable& var{get_variable(get_operand(f_abstracted))};

  EXPECT_EQ(var.get_type(), Variable::Type::BOOLEAN);
  EXPECT_PRED2(FormulaEqual, abstractor_[var], x_ + y_ <= 10);
  EXPECT_PRED2(VarEqual, abstractor_[x_ + y_ <= 10], var);
}

TEST_F(PredicateAbstractorTest, Geq) {
  // x + y >= 10 <-> !(x + y < 10)
  const Formula f{x_ + y_ >= 10};
  const Formula f_abstracted{abstractor_.Convert(f)};

  EXPECT_FALSE(is_variable(f));
  ASSERT_TRUE(is_negation(f_abstracted));
  ASSERT_TRUE(is_variable(get_operand(f_abstracted)));
  const Variable& var{get_variable(get_operand(f_abstracted))};

  EXPECT_EQ(var.get_type(), Variable::Type::BOOLEAN);
  EXPECT_PRED2(FormulaEqual, abstractor_[var], x_ + y_ < 10);
  EXPECT_PRED2(VarEqual, abstractor_[x_ + y_ < 10], var);
}

TEST_F(PredicateAbstractorTest, Lt) {
  // x + y < 10 <-> b
  const Formula f{x_ + y_ < 10};
  const Formula f_abstracted{abstractor_.Convert(f)};

  EXPECT_FALSE(is_variable(f));
  ASSERT_TRUE(is_variable(f_abstracted));
  const Variable& var{get_variable(f_abstracted)};

  EXPECT_EQ(var.get_type(), Variable::Type::BOOLEAN);
  EXPECT_PRED2(FormulaEqual, abstractor_[var], f);
  EXPECT_PRED2(VarEqual, abstractor_[f], var);
}

TEST_F(PredicateAbstractorTest, Leq) {
  // x + y <= 10 <-> b
  const Formula f{x_ + y_ <= 10};
  const Formula f_abstracted{abstractor_.Convert(f)};

  EXPECT_FALSE(is_variable(f));
  ASSERT_TRUE(is_variable(f_abstracted));
  const Variable& var{get_variable(f_abstracted)};

  EXPECT_EQ(var.get_type(), Variable::Type::BOOLEAN);
  EXPECT_PRED2(FormulaEqual, abstractor_[var], f);
  EXPECT_PRED2(VarEqual, abstractor_[f], var);
}

TEST_F(PredicateAbstractorTest, Conjunction) {
  // f₁ ∧ f₂ ∧ f₃ ∧ f₄ <-> !b₁ ∧ !b₂ ∧ b₃ ∧ !b₄
  const Formula f1{x_ >= y_};
  const Formula f2{y_ >= z_};
  const Formula f3{x_ + y_ <= 15};
  const Formula f4{y_ * z_ > 0};
  const Formula conjunction{f1 && f2 && f3 && f4};
  const set<Formula> operands{get_operands(conjunction)};

  const Formula conjunction_abstracted{abstractor_.Convert(conjunction)};
  ASSERT_TRUE(is_conjunction(conjunction_abstracted));
  const set<Formula> operands_abstracted{get_operands(conjunction_abstracted)};
  EXPECT_EQ(operands_abstracted.size(), operands.size());

  for (const Formula& f : operands_abstracted) {
    ASSERT_TRUE(is_variable(f) ||
                (is_negation(f) && is_variable(get_operand(f))));
    // if (is_variable(f)) {
    //   // Case: f = v.
    //   const Variable& var{get_variable(f)};
    //   const Formula& corresponding_f{abstractor_[var]};
    //   EXPECT_TRUE(operands.find(corresponding_f) != operands.end());
    // } else {
    //   // Case: f = !v.
    //   const Variable& var{get_variable(get_operand(f))};
    //   const Formula& corresponding_f{abstractor_[var]};
    //   EXPECT_TRUE(operands.find(corresponding_f) != operands.end());
    // }
  }
}

TEST_F(PredicateAbstractorTest, Disjunction) {
  // f₁ ∨ f₂ ∨ f₃ ∨ f₄ <-> b₁ ∨ b₂ ∨ b₃ ∨ b₄
  const Formula f1{x_ >= y_};
  const Formula f2{y_ >= z_};
  const Formula f3{x_ + y_ <= 15};
  const Formula f4{y_ * z_ > 0};
  const Formula disjunction{f1 || f2 || f3 || f4};
  const set<Formula> operands{get_operands(disjunction)};

  const Formula disjunction_abstracted{abstractor_.Convert(disjunction)};
  ASSERT_TRUE(is_disjunction(disjunction_abstracted));
  const set<Formula> operands_abstracted{get_operands(disjunction_abstracted)};
  EXPECT_EQ(operands_abstracted.size(), operands.size());

  for (const Formula& f : operands_abstracted) {
    ASSERT_TRUE(is_variable(f) ||
                (is_negation(f) && is_variable(get_operand(f))));
    // ASSERT_TRUE(is_variable(f));
    // const Variable& var{get_variable(f)};
    // const Formula& corresponding_f{abstractor_[var]};
    // EXPECT_TRUE(operands.find(corresponding_f) != operands.end());
  }
}

TEST_F(PredicateAbstractorTest, Negation) {
  // !(x + y >= 10) <-> x + y < 10
  const Formula f{x_ + y_ >= 10};
  const Formula not_f{!f};
  const Formula not_f_abstracted{abstractor_.Convert(not_f)};

  ASSERT_TRUE(is_variable(not_f_abstracted));
  const Variable& var{get_variable(not_f_abstracted)};
  EXPECT_EQ(var.get_type(), Variable::Type::BOOLEAN);
  EXPECT_PRED2(FormulaEqual, abstractor_[var], x_ + y_ < 10);
  EXPECT_PRED2(VarEqual, abstractor_[x_ + y_ < 10], var);
}

TEST_F(PredicateAbstractorTest, Forall) {
  // (∀x. x >= 0) <-> b
  const Formula f{forall({x_}, x_ >= 0)};
  const Formula f_abstracted{abstractor_.Convert(f)};
  ASSERT_TRUE(is_variable(f_abstracted));
  const Variable& var{get_variable(f_abstracted)};
  EXPECT_EQ(var.get_type(), Variable::Type::BOOLEAN);
  EXPECT_PRED2(FormulaEqual, abstractor_[var], f);
  EXPECT_PRED2(VarEqual, abstractor_[f], var);
}

}  // namespace
}  // namespace dreal
