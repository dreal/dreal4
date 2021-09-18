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

#include "dreal/api/api.h"
#include "dreal/symbolic/symbolic.h"

namespace dreal {
void synthesize_abs() {
  const Variable x{"x"};
  const Variable a{"a"};
  const Variable b{"b"};
  const Variable c{"c"};

  const Formula nested{
      imply(-1000 <= x && x <= 1000,
            imply(x >= c, abs(x) == a * x) && imply(x < c, abs(x) == b * x))};
  const Formula quantified{forall({x}, nested)};

  Config config;
  config.mutable_precision() = 0.001;
  config.mutable_use_polytope_in_forall() = true;
  config.mutable_use_local_optimization() = true;
  const auto result =
      CheckSatisfiability(-100 <= a && a <= 100 && -100 <= b && b <= 100 &&
                              -100 <= c && c <= 100 && quantified,
                          config);
  if (result) {
    std::cerr << *result << std::endl;
  } else {
    std::cerr << "Failed!" << std::endl;
  }
}
}  // namespace dreal

int main() { dreal::synthesize_abs(); }
