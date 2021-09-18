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
#include "dreal/util/tseitin_cnfizer.h"

#include <iostream>
#include <set>
#include <vector>

#include <gtest/gtest.h>

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/assert.h"

using std::set;
using std::vector;

namespace dreal {
namespace {

// Naive SAT solving process.
bool IsSatisfiable(const Formula& f) {
  if (is_true(f)) {
    return true;
  }
  if (is_false(f)) {
    return false;
  }
  const Variables& vars{f.GetFreeVariables()};
  DREAL_ASSERT(!vars.empty());
  const Variable& first_var{*vars.begin()};
  return IsSatisfiable(f.Substitute(first_var, Formula::True())) ||
         IsSatisfiable(f.Substitute(first_var, Formula::False()));
}

class TseitinCnfizerTest : public ::testing::Test {
 protected:
  ::testing::AssertionResult CnfChecker(const Formula& f) {
    const vector<Formula> clauses{cnfizer_.Convert(f)};
    const Formula f_cnf{
        make_conjunction(set<Formula>{clauses.begin(), clauses.end()})};
    // Check1: f_cnf should be in CNF.
    if (!is_cnf(f_cnf)) {
      return ::testing::AssertionFailure() << f_cnf << " is not in CNF.";
    }

    // Check2: f(b₁, b₂, b₃) is satisfiable iff f_cnf(b₁, b₂, b₃) is
    // satisfiable.
    for (const Formula& b1_val : {Formula::True(), Formula::False()}) {
      for (const Formula& b2_val : {Formula::True(), Formula::False()}) {
        for (const Formula& b3_val : {Formula::True(), Formula::False()}) {
          const bool sat_f{IsSatisfiable(f.Substitute(
              ExpressionSubstitution{},
              {{b1_, (b1_val)}, {b2_, (b2_val)}, {b3_, (b3_val)}}))};
          const bool sat_f_cnf{IsSatisfiable(
              f_cnf.Substitute(ExpressionSubstitution{},
                               {{b1_, b1_val}, {b2_, b2_val}, {b3_, b3_val}}))};
          if (sat_f != sat_f_cnf) {
            return ::testing::AssertionFailure()
                   << "The following formulas are not equi-satisfiable:\n"
                   << "f     = " << f << "\n"
                   << "f_cnf = " << f_cnf << "\n";
          }
        }
      }
    }
    return ::testing::AssertionSuccess();
  }

  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};

  const Variable b1_{"b1", Variable::Type::BOOLEAN};
  const Variable b2_{"b2", Variable::Type::BOOLEAN};
  const Variable b3_{"b3", Variable::Type::BOOLEAN};

  TseitinCnfizer cnfizer_;
};

TEST_F(TseitinCnfizerTest, Test) {
  vector<Formula> formulas;
  formulas.emplace_back(Formula{b1_});
  formulas.push_back(!b1_);
  formulas.push_back(b1_ || b2_);
  formulas.push_back(b1_ && b2_);
  formulas.push_back((b1_ && b2_) || (b1_ && !b3_));
  formulas.push_back((b1_ || b2_) && (b1_ || !b3_));

  for (const auto& f : formulas) {
    EXPECT_TRUE(CnfChecker(f));
  }
}

}  // namespace
}  // namespace dreal
