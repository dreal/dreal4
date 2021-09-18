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
#include "dreal/solver/context.h"

#include <gtest/gtest.h>

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/logging.h"

namespace dreal {
namespace {

class ContextTest : public ::testing::Test {
 protected:
  void SetUp() override { context_.DeclareVariable(x_); }

  const Variable x_{"x"};
  Context context_;
};

TEST_F(ContextTest, MultipleCheckSat) {
  context_.Assert(x_ >= 0);
  const auto result1 = context_.CheckSat();
  EXPECT_TRUE(result1);
  context_.Assert(x_ <= 5);
  const auto result2 = context_.CheckSat();
  EXPECT_TRUE(result2);
}

TEST_F(ContextTest, AssertionsAndBox) {
  const Formula f1{x_ >= 0};
  const Formula f2{x_ <= 5};
  const Formula f3{sin(x_) == 1.0};
  const Formula f4{cos(x_) == 0.0};
  context_.Assert(f1);
  context_.Assert(f2);
  context_.Assert(f3);
  context_.Assert(f4);

  const auto& assertions{context_.assertions()};
  EXPECT_EQ(assertions.size(), 2);
  EXPECT_TRUE(assertions[0].EqualTo(f3));
  EXPECT_TRUE(assertions[1].EqualTo(f4));

  const auto& box{context_.box()};
  EXPECT_EQ(box[x_].lb(), 0.0);
  EXPECT_EQ(box[x_].ub(), 5.0);
}

}  // namespace
}  // namespace dreal
