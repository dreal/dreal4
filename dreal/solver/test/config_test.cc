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
#include "dreal/solver/config.h"

#include <utility>

#include <gtest/gtest.h>

#include "dreal/api/api.h"
#include "dreal/solver/context.h"

namespace dreal {
namespace {

using std::pair;

// To save the branch variables in MyBrancher function.
std::vector<Variable> g_branch_variables;

int MyBrancher(const Box& box, const DynamicBitset& bitset, Box* left,
               Box* right) {
  DREAL_ASSERT(!bitset.none());

  const pair<double, int> max_diam_and_idx{FindMaxDiam(box, bitset)};
  const int branching_dim{max_diam_and_idx.second};
  if (branching_dim >= 0) {
    pair<Box, Box> bisected_boxes{box.bisect(branching_dim)};
    *left = std::move(bisected_boxes.first);
    *right = std::move(bisected_boxes.second);
    g_branch_variables.push_back(box.variable(branching_dim));
    return branching_dim;
  }
  return -1;
}

GTEST_TEST(Config, CustomBrancher) {
  // 0 ≤ x ≤ 5
  // 0 ≤ y ≤ 5
  // 0 ≤ z ≤ 5
  // 2x + y = z
  const Variable x{"x"};
  const Variable y{"y"};
  const Variable z{"z"};
  const Formula f1{0 <= x && x <= 5};
  const Formula f2{0 <= y && y <= 5};
  const Formula f3{0 <= z && z <= 5};
  const Formula f4{2 * x + y == z};

  Config config;
  config.mutable_brancher() = MyBrancher;

  // Checks the API returning an optional.
  auto result = CheckSatisfiability(f1 && f2 && f3 && f4, config);
  ASSERT_TRUE(result);

  EXPECT_EQ(g_branch_variables.size(), 42);
  EXPECT_EQ(g_branch_variables[0], y);
  EXPECT_EQ(g_branch_variables[1], z);
  EXPECT_EQ(g_branch_variables[2], x);
  EXPECT_EQ(g_branch_variables[3], y);
  EXPECT_EQ(g_branch_variables[4], z);
}

}  // namespace
}  // namespace dreal
