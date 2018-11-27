#include "dreal/symbolic/symbolic.h"

#include <iostream>
#include <type_traits>

#include <gtest/gtest.h>

#include "dreal/symbolic/symbolic_test_util.h"

using std::cout;
using std::endl;
using std::to_string;
using std::vector;

namespace dreal {
namespace {

class SymbolicTest : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};

  const Variable b1_{"B1", Variable::Type::BOOLEAN};
  const Variable b2_{"B2", Variable::Type::BOOLEAN};
  const Variable b3_{"B3", Variable::Type::BOOLEAN};
};

TEST_F(SymbolicTest, Imply) {
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

TEST_F(SymbolicTest, Iff) {
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

TEST_F(SymbolicTest, Equality) {
  {
    // Boolean Variable == Boolean Variable.
    const Formula f{b1_ == b2_};
    EXPECT_PRED2(FormulaEqual, f, iff(b1_, b2_));
  }

  {
    // Scalar Variable == Scalar Variable.
    const Formula f{x_ == y_};
    EXPECT_TRUE(is_relational(f));
  }

  {
    // Expression == Scalar Variable.
    const Formula f{(x_ + 1) == y_};
    EXPECT_TRUE(is_relational(f));
  }

  // Scalar Variable == Expression.
  {
    const Formula f{y_ == (x_ + 1)};
    EXPECT_TRUE(is_relational(f));
  }

  // Expression == Expression.
  {
    const Formula f{y_ == x_};
    EXPECT_TRUE(is_relational(f));
  }

  {
    // Boolean Variable == Formula.
    const Formula f{b1_ == (x_ > y_)};
    EXPECT_PRED2(FormulaEqual, f, iff(b1_, x_ > y_));
  }

  {
    // Formula == Boolean Variable.
    const Formula f{(x_ > y_) == b1_};
    EXPECT_PRED2(FormulaEqual, f, iff(b1_, x_ > y_));
  }

  {
    // Formula == Formula.
    const Formula f{(y_ > z_) == (x_ > y_)};
    EXPECT_PRED2(FormulaEqual, f, iff(y_ > z_, x_ > y_));
  }

  {
    Formula f;
    // Boolean Variable == Scalar Variable: => EXCEPTION.
    EXPECT_THROW(f = (b1_ == y_), std::runtime_error);

    // Scalar Variable == Boolean Variable: => EXCEPTION.
    EXPECT_THROW(f = (y_ == b1_), std::runtime_error);

    // Boolean Variable == Expression: => EXCEPTION.
    EXPECT_THROW(f = (b1_ == (y_ + 3)), std::runtime_error);

    // Expression == Boolean Variable: => EXCEPTION.
    EXPECT_THROW(f = ((x_ + 3) == b1_), std::runtime_error);

    // Scalar Variable == Formula: => EXCEPTION.
    EXPECT_THROW(f = (x_ == (x_ > 3)), std::runtime_error);

    // Formula == Scalar Variable: => EXCEPTION.
    EXPECT_THROW(f = ((x_ > 3) == x_), std::runtime_error);

    // Expression == Formula: => Compile Error.
    // EXPECT_THROW(f = ((x_ + 3) == (x_ > 3)), std::runtime_error);

    // Formula == Expression: => Compile Error.
    // EXPECT_THROW(f = ((x_ > 3) == (x_ + 3)), std::runtime_error);
  }
}

TEST_F(SymbolicTest, Inequality) {
  {
    // Boolean Variable != Boolean Variable.
    const Formula f{b1_ != b2_};
    EXPECT_PRED2(FormulaEqual, f, !iff(b1_, b2_));
  }

  {
    // Scalar Variable != Scalar Variable.
    const Formula f{x_ != y_};
    EXPECT_TRUE(is_relational(f));
  }

  {
    // Expression != Scalar Variable.
    const Formula f{(x_ + 1) != y_};
    EXPECT_TRUE(is_relational(f));
  }

  // Scalar Variable != Expression.
  {
    const Formula f{y_ != (x_ + 1)};
    EXPECT_TRUE(is_relational(f));
  }

  // Expression != Expression.
  {
    const Formula f{y_ != x_};
    EXPECT_TRUE(is_relational(f));
  }

  {
    // Boolean Variable != Formula.
    const Formula f{b1_ != (x_ > y_)};
    EXPECT_PRED2(FormulaEqual, f, !iff(b1_, x_ > y_));
  }

  {
    // Formula != Boolean Variable.
    const Formula f{(x_ > y_) != b1_};
    EXPECT_PRED2(FormulaEqual, f, !iff(b1_, x_ > y_));
  }

  {
    // Formula != Formula.
    const Formula f{(y_ > z_) != (x_ > y_)};
    EXPECT_PRED2(FormulaEqual, f, !iff(y_ > z_, x_ > y_));
  }

  {
    Formula f;
    // Boolean Variable != Scalar Variable: => EXCEPTION.
    EXPECT_THROW(f = (b1_ != y_), std::runtime_error);

    // Scalar Variable != Boolean Variable: => EXCEPTION.
    EXPECT_THROW(f = (y_ != b1_), std::runtime_error);

    // Boolean Variable != Expression: => EXCEPTION.
    EXPECT_THROW(f = (b1_ != (y_ + 3)), std::runtime_error);

    // Expression != Boolean Variable: => EXCEPTION.
    EXPECT_THROW(f = ((x_ + 3) != b1_), std::runtime_error);

    // Scalar Variable != Formula: => EXCEPTION.
    EXPECT_THROW(f = (x_ != (x_ > 3)), std::runtime_error);

    // Formula != Scalar Variable: => EXCEPTION.
    EXPECT_THROW(f = ((x_ > 3) != x_), std::runtime_error);

    // Expression != Formula: => Compile Error.
    // EXPECT_THROW(f = ((x_ + 3) != (x_ > 3)), std::runtime_error);

    // Formula != Expression: => Compile Error.
    // EXPECT_THROW(f = ((x_ > 3) != (x_ + 3)), std::runtime_error);
  }
}

TEST_F(SymbolicTest, CreateVectorContinuous) {
  const vector<Variable> v{CreateVector("x", 5)};
  for (int i = 0; i < 5; ++i) {
    EXPECT_EQ(v[i].get_name(), "x" + to_string(i));
    EXPECT_EQ(v[i].get_type(), Variable::Type::CONTINUOUS);
  }
}

TEST_F(SymbolicTest, CreateVectorInteger) {
  const vector<Variable> v{CreateVector("y", 10, Variable::Type::INTEGER)};
  for (int i = 0; i < 10; ++i) {
    EXPECT_EQ(v[i].get_name(), "y" + to_string(i));
    EXPECT_EQ(v[i].get_type(), Variable::Type::INTEGER);
  }
}

TEST_F(SymbolicTest, Sum) {
  const Expression e1{x_ + 1.0};
  const Expression e2{y_ + 2.0};
  const Expression e3{x_ * y_ * z_};
  EXPECT_PRED2(ExprEqual, Sum({}), Expression::Zero());
  EXPECT_PRED2(ExprEqual, Sum({e1}), e1);
  EXPECT_PRED2(ExprEqual, (Sum({e1, e2, e3})), e1 + e2 + e3);
}

TEST_F(SymbolicTest, Prod) {
  const Expression e1{x_ + 1.0};
  const Expression e2{y_ + 2.0};
  const Expression e3{x_ * y_ * z_};
  EXPECT_PRED2(ExprEqual, Prod({}), Expression::One());
  EXPECT_PRED2(ExprEqual, Prod({e1}), e1);
  EXPECT_PRED2(ExprEqual, (Prod({e1, e2, e3})), e1 * e2 * e3);
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
