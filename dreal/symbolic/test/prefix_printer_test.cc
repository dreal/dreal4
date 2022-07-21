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
#include "dreal/symbolic/prefix_printer.h"

#include <cmath>

#include <gtest/gtest.h>

namespace dreal {
namespace {

class PrefixPrinterTest : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};

  const Variable i1_{"i1", Variable::Type::INTEGER};
  const Variable i2_{"i2", Variable::Type::INTEGER};
  const Variable i3_{"i3", Variable::Type::INTEGER};

  const Variable b1_{"b1", Variable::Type::BOOLEAN};
  const Variable b2_{"b2", Variable::Type::BOOLEAN};
  const Variable b3_{"b3", Variable::Type::BOOLEAN};
};

TEST_F(PrefixPrinterTest, Variable) {
  const Expression e{x_};
  EXPECT_EQ(ToPrefix(e), "x");
}

TEST_F(PrefixPrinterTest, Constant1) {
  const Expression e{3.0};
  EXPECT_EQ(ToPrefix(e), "3");
}

TEST_F(PrefixPrinterTest, Constant2) {
  const Expression e{M_PI};
  EXPECT_EQ(ToPrefix(e), "3.141592653589793116");
}

TEST_F(PrefixPrinterTest, Constant3) {
  const Expression e{-3.0};
  EXPECT_EQ(ToPrefix(e), "(- 3)");
}

TEST_F(PrefixPrinterTest, Constant4) {
  const Expression e{-M_PI};
  EXPECT_EQ(ToPrefix(e), "(- 3.141592653589793116)");
}

TEST_F(PrefixPrinterTest, Addition) {
  const Expression e{-3 + x_ - 2 * y_ + 3 * z_};
  EXPECT_EQ(ToPrefix(e), "(+ (- 3) x (* (- 2) y) (* 3 z))");
}

TEST_F(PrefixPrinterTest, Multiplication) {
  const Expression e{-2 * pow(x_, -2) * 2 * y_ * 3 * pow(z_, 5)};
  EXPECT_EQ(ToPrefix(e), "(* (- 12) (^ x (- 2)) y (^ z 5))");
}

TEST_F(PrefixPrinterTest, Division) {
  const Expression e{x_ / y_};
  EXPECT_EQ(ToPrefix(e), "(/ x y)");
}

TEST_F(PrefixPrinterTest, Log) {
  const Expression e{log(x_)};
  EXPECT_EQ(ToPrefix(e), "(log x)");
}

TEST_F(PrefixPrinterTest, Abs) {
  const Expression e{abs(x_)};
  EXPECT_EQ(ToPrefix(e), "(abs x)");
}

TEST_F(PrefixPrinterTest, Exp) {
  const Expression e{exp(x_)};
  EXPECT_EQ(ToPrefix(e), "(exp x)");
}

TEST_F(PrefixPrinterTest, Sqrt) {
  const Expression e{sqrt(x_)};
  EXPECT_EQ(ToPrefix(e), "(sqrt x)");
}

TEST_F(PrefixPrinterTest, Pow) {
  const Expression e{pow(x_, y_)};
  EXPECT_EQ(ToPrefix(e), "(^ x y)");
}

TEST_F(PrefixPrinterTest, Sin) {
  const Expression e{sin(x_)};
  EXPECT_EQ(ToPrefix(e), "(sin x)");
}

TEST_F(PrefixPrinterTest, Cos) {
  const Expression e{cos(x_)};
  EXPECT_EQ(ToPrefix(e), "(cos x)");
}

TEST_F(PrefixPrinterTest, Tan) {
  const Expression e{tan(x_)};
  EXPECT_EQ(ToPrefix(e), "(tan x)");
}

TEST_F(PrefixPrinterTest, Asin) {
  const Expression e{asin(x_)};
  EXPECT_EQ(ToPrefix(e), "(asin x)");
}

TEST_F(PrefixPrinterTest, Acos) {
  const Expression e{acos(x_)};
  EXPECT_EQ(ToPrefix(e), "(acos x)");
}

TEST_F(PrefixPrinterTest, Atan) {
  const Expression e{atan(x_)};
  EXPECT_EQ(ToPrefix(e), "(atan x)");
}

TEST_F(PrefixPrinterTest, Atan2) {
  const Expression e{atan2(x_, y_)};
  EXPECT_EQ(ToPrefix(e), "(atan2 x y)");
}

TEST_F(PrefixPrinterTest, Sinh) {
  const Expression e{sinh(x_)};
  EXPECT_EQ(ToPrefix(e), "(sinh x)");
}

TEST_F(PrefixPrinterTest, Cosh) {
  const Expression e{cosh(x_)};
  EXPECT_EQ(ToPrefix(e), "(cosh x)");
}

TEST_F(PrefixPrinterTest, Tanh) {
  const Expression e{tanh(x_)};
  EXPECT_EQ(ToPrefix(e), "(tanh x)");
}

TEST_F(PrefixPrinterTest, Min) {
  const Expression e{min(x_, y_)};
  EXPECT_EQ(ToPrefix(e), "(min x y)");
}

TEST_F(PrefixPrinterTest, Max) {
  const Expression e{max(x_, y_)};
  EXPECT_EQ(ToPrefix(e), "(max x y)");
}

TEST_F(PrefixPrinterTest, IfThenElse) {
  const Expression e{if_then_else(x_ > y_, x_, y_)};
  EXPECT_EQ(ToPrefix(e), "(ite (> x y) x y)");
}

TEST_F(PrefixPrinterTest, False) { EXPECT_EQ(ToPrefix(x_ != x_), "false"); }

TEST_F(PrefixPrinterTest, True) { EXPECT_EQ(ToPrefix(x_ == x_), "true"); }

TEST_F(PrefixPrinterTest, FormulaVariable) {
  EXPECT_EQ(ToPrefix(Formula{b1_}), "b1");
}

TEST_F(PrefixPrinterTest, EqualTo) { EXPECT_EQ(ToPrefix(x_ == y_), "(= x y)"); }

TEST_F(PrefixPrinterTest, NotEqualTo) {
  EXPECT_EQ(ToPrefix(x_ != y_), "(not (= x y))");
}

TEST_F(PrefixPrinterTest, GT) { EXPECT_EQ(ToPrefix(x_ > y_), "(> x y)"); }

TEST_F(PrefixPrinterTest, GTE) { EXPECT_EQ(ToPrefix(x_ >= y_), "(>= x y)"); }

TEST_F(PrefixPrinterTest, LT) { EXPECT_EQ(ToPrefix(x_ < y_), "(< x y)"); }

TEST_F(PrefixPrinterTest, LTE) { EXPECT_EQ(ToPrefix(x_ <= y_), "(<= x y)"); }

TEST_F(PrefixPrinterTest, And) {
  EXPECT_EQ(ToPrefix(x_ <= y_ && y_ <= z_ && z_ <= x_),
            "(and (<= x y) (<= y z) (<= z x))");
}

TEST_F(PrefixPrinterTest, Or) {
  EXPECT_EQ(ToPrefix(x_ <= y_ || y_ <= z_ || z_ <= x_),
            "(or (<= x y) (<= y z) (<= z x))");
}

TEST_F(PrefixPrinterTest, Negation) {
  EXPECT_EQ(ToPrefix(!(x_ <= y_)), "(not (<= x y))");
}

}  // namespace
}  // namespace dreal
