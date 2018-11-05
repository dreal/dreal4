#include "dreal/util/math.h"

#include <cmath>
#include <limits>

#include "dreal/util/exception.h"

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

// NOLINTNEXTLINE(runtime/int)
int convert_long_to_int(const long v) {
  if (numeric_limits<int>::min() <= v && v <= numeric_limits<int>::max()) {
    return v;
  } else {
    throw DREAL_RUNTIME_ERROR("Fail to convert a long value {} to int", v);
  }
}

// NOLINTNEXTLINE(runtime/int)
double convert_long_to_double(const long v) {
  // NOLINTNEXTLINE(runtime/int)
  constexpr long m{1l << numeric_limits<double>::digits};
  if (-m <= v && v <= m) {
    return v;
  } else {
    throw DREAL_RUNTIME_ERROR("Fail to convert a long value {} to double", v);
  }
}

}  // namespace dreal
