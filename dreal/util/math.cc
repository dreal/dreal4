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
  double intpart;  // dummy variable
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
  constexpr int64_t m{1ul << numeric_limits<double>::digits};
  if (-m <= v && v <= m) {
    return v;
  } else {
    throw DREAL_RUNTIME_ERROR("Fail to convert a int64_t value {} to double",
                              v);
  }
}

}  // namespace dreal
