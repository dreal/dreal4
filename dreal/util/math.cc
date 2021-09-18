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
#include "dreal/util/math.h"

#include <cmath>
#include <iostream>
#include <limits>

#include "dreal/util/exception.h"

using std::int64_t;
using std::modf;
using std::numeric_limits;

namespace dreal {
bool is_integer(const double v) {
  // v should be in [int_min, int_max].
  if (!((numeric_limits<int>::lowest() <= v) &&
        (v <= numeric_limits<int>::max()))) {
    return false;
  }
  double intpart{};  // dummy variable
  return modf(v, &intpart) == 0.0;
}

int convert_int64_to_int(const int64_t v) {
  if (numeric_limits<int>::min() <= v && v <= numeric_limits<int>::max()) {
    return v;
  } else {
    throw DREAL_RUNTIME_ERROR("Fail to convert a int64_t value {} to int", v);
  }
}

double convert_int64_to_double(const int64_t v) {
  constexpr int64_t m{
      1UL << static_cast<unsigned>(numeric_limits<double>::digits)};
  if (-m <= v && v <= m) {
    return v;
  } else {
    throw DREAL_RUNTIME_ERROR("Fail to convert a int64_t value {} to double",
                              v);
  }
}

}  // namespace dreal
