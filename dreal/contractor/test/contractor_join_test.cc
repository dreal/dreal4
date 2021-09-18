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
#include "dreal/contractor/contractor_join.h"

#include <iostream>
#include <vector>

#include <gtest/gtest.h>

#include "dreal/contractor/contractor_ibex_fwdbwd.h"
#include "dreal/contractor/contractor_status.h"
#include "dreal/solver/config.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/interval.h"

namespace dreal {
namespace {

using std::vector;

class ContractorJoinTest : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};
  const vector<Variable> vars_{{x_, y_, z_}};
  Box box_{vars_};
};

TEST_F(ContractorJoinTest, Sat) {
  const Formula f1{cos(x_) >= sin(y_) - 0.1};
  const Formula f2{cos(x_) <= sin(y_) + 0.1};
  box_[x_] = Box::Interval(0.0, 3.14 / 2);
  box_[y_] = Box::Interval(0.2, 0.3);
  box_[z_] = Box::Interval(0.0, 1.0);
  ContractorStatus cs{box_};
  Config config{};
  const Contractor ctc1 = make_contractor_ibex_fwdbwd(f1, box_, config);
  const Contractor ctc2 = make_contractor_ibex_fwdbwd(f2, box_, config);
  const Contractor ctc = make_contractor_join({ctc1, ctc2}, config);

  // Inputs
  EXPECT_TRUE(ctc.input()[0]);
  EXPECT_TRUE(ctc.input()[1]);
  EXPECT_FALSE(ctc.input()[2]);

  // Before pruning, the box is not empty.
  EXPECT_FALSE(cs.box().empty());

  ctc.Prune(&cs);

  // After pruning, the box is still not empty.
  EXPECT_FALSE(cs.box().empty());
}

}  // namespace
}  // namespace dreal
