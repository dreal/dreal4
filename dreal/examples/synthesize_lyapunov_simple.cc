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
#include "dreal/examples/control.h"

#include <iostream>

namespace dreal {
namespace {

using std::cout;
using std::endl;

void synthesize_lyapunov_simple() {
  //           ẋ₁ = -x₂ - x₁³
  //           ẋ₂ =  x₁ - x₂³
  // Candidate V  = c₁x₁² + c₂x₂² + c₃x₁x₂.
  const Variable x1{"x1"};
  const Variable x2{"x2"};

  const Variable c1{"c1"};
  const Variable c2{"c2"};
  const Variable c3{"c3"};

  Config config;
  config.mutable_precision() = 0.0001;
  config.mutable_use_polytope_in_forall() = true;
  config.mutable_use_local_optimization() = true;

  // clang-format off
  Expression V = c1 * x1 * x1 + c2 * x2 * x2 + c3 * x1 * x2;
  const auto result =
      SynthesizeLyapunov({x1, x2}, {-x2 - pow(x1, 3), x1 - pow(x2, 3)},
                         V,
                         0.2, 1.0,  /* lb&ub of ball */
                         0, 2, /* lb&ub of c_i */
                         config);
  // clang-format on
  if (result) {
    cout << "Found:" << endl << *result << endl;
    for (const Variable& var : result->variables()) {
      V = V.Substitute(var, (*result)[var].mid());
    }
    cout << "V = " << V << endl;
  } else {
    cout << "Not found." << endl;
  }
}
}  // namespace
}  // namespace dreal

int main() { dreal::synthesize_lyapunov_simple(); }
