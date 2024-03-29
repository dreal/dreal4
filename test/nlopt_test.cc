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
#include <cmath>
#include <iostream>
#include <vector>

#include <gtest/gtest.h>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#include <nlopt.hpp>
#pragma GCC diagnostic pop

namespace {

using std::cos;
using std::sin;
using std::vector;

// object function: sin(x₀) * cos(x₁)
double obj(unsigned, const double* x, double* grad, void*) {
  if (grad) {
    grad[0] = cos(x[0]) * cos(x[1]);
    grad[1] = -sin(x[0]) * sin(x[1]);
  }
  return sin(x[0]) * cos(x[1]);
}

GTEST_TEST(NloptTest, Test) {
  nlopt::opt opt(nlopt::LD_SLSQP, 2);

  // lower bound
  //    0 <= x₀
  //    0 <= x₀
  vector<double> lb(2);
  lb[0] = 0;
  lb[1] = 0;
  opt.set_lower_bounds(lb);

  // upper bound
  //    x₀ <= 10
  //    x₁ <= 10
  vector<double> ub(2);
  ub[0] = 10;
  ub[1] = 10;
  opt.set_upper_bounds(ub);

  // set objective function
  opt.set_min_objective(obj, nullptr);

  // set tolerance
  opt.set_ftol_rel(1e-4);

  // set initial point
  //    init[0] = 5.0
  //    init[1] = 5.0
  vector<double> init{5.0, 5.0};

  // Call optimization
  double sol = 0.0;
  const nlopt::result result{opt.optimize(init, sol)};

  // Print result
  EXPECT_NEAR(init[0], 4.7126753944645801, 0.0001);
  EXPECT_NEAR(init[1], 6.2834450901676488, 0.0001);
  EXPECT_GT(result, 0);
  EXPECT_NEAR(sol, -1, 1e-4);
}
}  // namespace
