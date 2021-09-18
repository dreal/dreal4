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
#include <numeric>
#include <ostream>
#include <vector>

#include "dreal/examples/control.h"

namespace dreal {
namespace {

using std::accumulate;
using std::cout;
using std::endl;
using std::vector;

void check_lyapunov_example1() {
  // ẋ₁ = x₂
  // ẋ₂ = -sin(x₁)
  // V  = (1 - cos(x₁)) + 0.5x₂²
  const Variable x1{"x1"};
  const Variable x2{"x2"};
  Config config;
  config.mutable_precision() = 1e-5;
  const auto result =
      CheckLyapunov({x1, x2}, {x2, -sin(x1)}, (1 - cos(x1)) + 0.5 * x2 * x2,
                    0.001, M_PI * M_PI, config);
  if (result) {
    std::cerr << "Not a L-function. Here is a counterexample:\n"
              << *result << std::endl;
  } else {
    std::cerr << "L function!" << std::endl;
  }
}

void check_lyapunov_example2() {
  // ẋ₁ = -x₂ - x₁³
  // ẋ₂ =  x₁ - x₂³
  // V  = x₁² + x₂²
  const Variable x1{"x1"};
  const Variable x2{"x2"};
  Config config;
  config.mutable_precision() = 1e-5;
  const auto result =
      CheckLyapunov({x1, x2}, {-x2 - pow(x1, 3), x1 - pow(x2, 3)},
                    x1 * x1 + x2 * x2, 0.1, 0.5, config);
  if (result) {
    std::cerr << "Not a L-function. Here is a counterexample:\n"
              << *result << std::endl;
  } else {
    std::cerr << "L function!" << std::endl;
  }
}
}  // namespace
}  // namespace dreal

int main() {
  dreal::check_lyapunov_example1();
  dreal::check_lyapunov_example2();
}
