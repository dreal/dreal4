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
#include "dreal/contractor/contractor_integer.h"

#include <iostream>

#include <gtest/gtest.h>

#include "dreal/contractor/contractor_status.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {
namespace {

using std::vector;

class ContractorIntegerTest : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::INTEGER};
  const Variable z_{"z", Variable::Type::INTEGER};
  const vector<Variable> vars_{{x_, y_, z_}};
  Box box_{vars_};
};

TEST_F(ContractorIntegerTest, Sat) {
  box_[x_] = Box::Interval(-0.2, 0.3);      // x : Real
  box_[y_] = Box::Interval(0.0, 3.14 / 2);  // y : Int
  box_[z_] = Box::Interval(0.0, 1.0);       // z : Int
  ContractorStatus cs{box_};

  Contractor ctc{make_contractor_integer(box_, Config{})};

  // Inputs: only int variables (y and z)
  EXPECT_FALSE(ctc.input()[0]);
  EXPECT_TRUE(ctc.input()[1]);
  EXPECT_TRUE(ctc.input()[2]);

  // Before pruning, the box is not empty.
  EXPECT_FALSE(cs.box().empty());

  ctc.Prune(&cs);

  // After pruning, the box is still not empty.
  EXPECT_FALSE(cs.box().empty());

  // x : [-0.2, 0.3] → [-0.2, 0.3]  // no change
  // y : [0.0, 1.57] → [0.0, 1.0]
  // z : [0.0, 1.0]  → [0.0, 1.0]   // no change
  EXPECT_EQ(cs.box()[x_], Box::Interval(-0.2, 0.3));
  EXPECT_EQ(cs.box()[y_], Box::Interval(0.0, 1.0));
  EXPECT_EQ(cs.box()[z_], Box::Interval(0.0, 1.0));

  // // Outputs. Only y is changed.
  EXPECT_FALSE(cs.output()[0]);
  EXPECT_TRUE(cs.output()[1]);
  EXPECT_FALSE(cs.output()[2]);
}

TEST_F(ContractorIntegerTest, Unsat) {
  box_[x_] = Box::Interval(-0.2, 0.3);  // x : Real
  box_[y_] = Box::Interval(0.5, 0.8);   // y : Int
  box_[z_] = Box::Interval(0.0, 1.0);   // z : Int
  ContractorStatus cs{box_};

  Contractor ctc{make_contractor_integer(box_, Config{})};

  // Inputs: only int variables (y and z)
  EXPECT_FALSE(ctc.input()[0]);
  EXPECT_TRUE(ctc.input()[1]);
  EXPECT_TRUE(ctc.input()[2]);

  // Before pruning, the box is not empty. (because of y).
  EXPECT_FALSE(cs.box().empty());

  ctc.Prune(&cs);

  // After pruning, the box is empty.
  EXPECT_TRUE(cs.box().empty());

  // // Outputs. All dimensions are changed.
  EXPECT_TRUE(cs.output()[0]);
  EXPECT_TRUE(cs.output()[1]);
  EXPECT_TRUE(cs.output()[2]);
}
}  // namespace
}  // namespace dreal
