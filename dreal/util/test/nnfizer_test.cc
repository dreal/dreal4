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
#include "dreal/util/nnfizer.h"

#include <iostream>

#include <gtest/gtest.h>

#include "dreal/symbolic/symbolic.h"
#include "dreal/symbolic/symbolic_test_util.h"

namespace dreal {
namespace {

class NnfizerTest : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};

  const Variable b1_{"b1", Variable::Type::BOOLEAN};
  const Variable b2_{"b2", Variable::Type::BOOLEAN};
  const Variable b3_{"b3", Variable::Type::BOOLEAN};

  const Nnfizer converter_{};
};

TEST_F(NnfizerTest, NNFNoChanges) {
  // No Changes: True
  EXPECT_PRED2(FormulaEqual, converter_.Convert(Formula::True()),
               Formula::True());

  // No Changes: False
  EXPECT_PRED2(FormulaEqual, converter_.Convert(Formula::False()),
               Formula::False());

  // No Changes: Variables
  EXPECT_PRED2(FormulaEqual, converter_.Convert(Formula{b1_}), Formula{b1_});
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!b1_), !b1_);

  // No Changes: x ≥ y ∧ y ≤ z
  const Formula f1{x_ >= y_ && y_ <= z_};
  EXPECT_PRED2(FormulaEqual, converter_.Convert(f1), f1);

  // No Changes.: x > y ∨ y < z
  const Formula f2{x_ > y_ || y_ < z_};
  EXPECT_PRED2(FormulaEqual, converter_.Convert(f2), f2);

  // No Changes: ∀x. x + y ≥ x
  const Formula f4{forall({x_}, x_ + y_ >= x_)};
  EXPECT_PRED2(FormulaEqual, converter_.Convert(f4), f4);
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!f4), !f4);
}

TEST_F(NnfizerTest, NNFRelational) {
  // ¬(x ≥ y) ∧ ¬(y ≤ z)  ==>  ¬(x ≥ y) ∧ ¬(y ≤ z)
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!(x_ >= y_) && !(y_ <= z_)),
               !(x_ >= y_) && !(y_ <= z_));

  // ¬(x ≥ y ∧ y ≤ z)  ==>  ¬(x ≥ y) ∨ ¬(y ≤ z)
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!(x_ >= y_ && y_ <= z_)),
               !(x_ >= y_) || !(y_ <= z_));

  // ¬(x > y) ∨ ¬(y < z)  ==>  ¬(x > y) ∨ ¬(y < z)
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!(x_ > y_) || !(y_ < z_)),
               !(x_ > y_) || !(y_ < z_));

  // ¬(x > y ∨ y < z)  ==>  ¬(x > y) ∧ ¬(y < z)
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!(x_ > y_ || y_ < z_)),
               !(x_ > y_) && !(y_ < z_));

  // ¬(x ≠ y) ∧ ¬(y = z)  ==>  ¬(x ≠ y) ∧ ¬(y = z)
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!(x_ != y_) && !(y_ == z_)),
               !(x_ != y_) && !(y_ == z_));

  // ¬(x ≠ y ∧ y = z)  ==>  ¬(x ≠ y) ∧ ¬(y = z)
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!(x_ != y_ && y_ == z_)),
               !(x_ != y_) || !(y_ == z_));
}

TEST_F(NnfizerTest, NNFBoolean) {
  // ¬(b₁ ∨ ¬(b₂ ∧ b₃))  ==>  ¬b₁ ∧ b₂ ∧ b₃
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!(b1_ || !(b2_ && b3_))),
               !b1_ && b2_ && b3_);

  // ¬(b₁ ∨ ¬(b₂ ∨ b₃))  ==>  ¬b₁ ∧ (b₂ ∨ b₃)
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!(b1_ || !(b2_ || b3_))),
               !b1_ && (b2_ || b3_));

  // ¬(b₁ ∧ ¬(b₂ ∨ b₃))  ==>  ¬b₁ ∨ b₂ ∨ b₃
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!(b1_ && !(b2_ || b3_))),
               !b1_ || b2_ || b3_);

  // ¬(b₁ ∧ ¬(b₂ ∧ b₃))  ==>  ¬b₁ ∨ (b₂ ∧ b₃)
  EXPECT_PRED2(FormulaEqual, converter_.Convert(!(b1_ && !(b2_ && b3_))),
               !b1_ || (b2_ && b3_));
}
}  // namespace
}  // namespace dreal
