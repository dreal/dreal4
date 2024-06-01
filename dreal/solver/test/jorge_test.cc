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
#include <iostream>
#include <vector>

#include <gtest/gtest.h>

#include "dreal/solver/context.h"
#include "dreal/symbolic/symbolic.h"

namespace dreal {
namespace {

using std::cerr;
using std::endl;
using std::vector;

GTEST_TEST(Test, Example) {
  // -----------------
  // Declare variables
  // -----------------
  const Variable s0_v1{"s0.v1", Variable::Type::BOOLEAN};
  const Variable s0_v2{"s0.v2", Variable::Type::BOOLEAN};
  const Variable s0_v3{"s0.v3", Variable::Type::CONTINUOUS};
  const Variable s0_v4{"s0.v4", Variable::Type::CONTINUOUS};

  const Variable s1_v1{"s1.v1", Variable::Type::BOOLEAN};
  const Variable s1_v2{"s1.v2", Variable::Type::BOOLEAN};
  const Variable s1_v3{"s1.v3", Variable::Type::CONTINUOUS};
  const Variable s1_v4{"s1.v4", Variable::Type::CONTINUOUS};

  const Variable s2_v1{"s2.v1", Variable::Type::BOOLEAN};
  const Variable s2_v2{"s2.v2", Variable::Type::BOOLEAN};
  const Variable s2_v3{"s2.v3", Variable::Type::CONTINUOUS};
  const Variable s2_v4{"s2.v4", Variable::Type::CONTINUOUS};

  // ----------
  // Assertions
  // ----------
  vector<Formula> assertions;

  const Formula assert1{!s0_v2 && !(0.25 <= pow(s0_v3, 2) + pow(s0_v4, 2))};

  const Formula assert2_1{
      (s0_v1 || s0_v2 ||
       ((98 * s0_v3 + 200 * s0_v4 + 2 * s1_v3 + -200 * pow(s0_v3, 2) * s0_v4 +
             -70 * pow(s0_v3, 2) + -100 * pow(s0_v3, 3) ==
         -70) &&
        (146 * s0_v3 + 102 * s0_v4 + -2 * s1_v4 + 140 * s0_v3 * s0_v4 +
             200 * s0_v3 * pow(s0_v4, 2) + 100 * pow(s0_v3, 2) * s0_v4 ==
         0)))};

  const Formula assert2_2{(s0_v1 || (s0_v2 == s1_v2))};

  const Formula assert2_3{s0_v1 || (s0_v3 == s1_v3 && s0_v4 == s1_v4) ||
                          !s0_v2};

  const Formula assert2_4{((s1_v2 && (s0_v3 == s1_v3) && (s0_v4 == s1_v4) &&
                            (1.5 <= s0_v3) && !s0_v2) ||
                           (s1_v2 && (s0_v3 == s1_v3) && (s0_v4 == s1_v4) &&
                            (s0_v3 <= -1.5) && !s0_v2) ||
                           !s0_v1)};

  const Formula assert3_1{
      (s1_v1 || s1_v2 ||
       ((98 * s1_v3 + 200 * s1_v4 + 2 * s2_v3 + -200 * pow(s1_v3, 2) * s1_v4 +
             -70 * pow(s1_v3, 2) + -100 * pow(s1_v3, 3) ==
         -70) &&
        (146 * s1_v3 + 102 * s1_v4 + -2 * s2_v4 + 140 * s1_v3 * s1_v4 +
             200 * s1_v3 * pow(s1_v4, 2) + 100 * pow(s1_v3, 2) * s1_v4 ==
         0)))};

  const Formula assert3_2{(s1_v1 || (s1_v2 == s2_v2))};

  const Formula assert3_3{s1_v1 || (s1_v3 == s2_v3 && s1_v4 == s2_v4) ||
                          !s1_v2};

  const Formula assert3_4{((s2_v2 && (s1_v3 == s2_v3) && (s1_v4 == s2_v4) &&
                            (1.5 <= s1_v3) && !s1_v2) ||
                           (s2_v2 && (s1_v3 == s2_v3) && (s1_v4 == s2_v4) &&
                            (s1_v3 <= -1.5) && !s1_v2) ||
                           !s1_v1)};

  const Formula assert4{s2_v2};

  assertions.push_back(assert1);
  assertions.push_back(assert2_1 && assert2_2 && assert2_3 && assert2_4);
  assertions.push_back(assert3_1 && assert3_2 && assert3_3 && assert3_4);
  assertions.push_back(assert4);

  // ----------------------------
  // Add variables and assertions
  // ----------------------------
  Context ctx;
  for (const Formula& f : assertions) {
    for (const Variable& v : f.GetFreeVariables()) {
      ctx.DeclareVariable(v);
    }
    ctx.Assert(f);
  }

  // --------
  // CheckSat
  // --------
  const auto result = ctx.CheckSat();
  EXPECT_TRUE(result);
  cerr << "delta-SAT" << endl;
  cerr << *result << endl;
}

}  // namespace
}  // namespace dreal
