#include "dreal/util/math.h"

#include <cmath>

#include "dreal/util/exception.h"

using std::modf;
using std::numeric_limits;

static const int64_t MAX_SAFE_INT_DBL = 9007199254740991L;  // 2**53-1

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

int64_t strtol_checked(const char *s) {
  double d = strtod_checked(s);
  if (!is_integer(d) || d > MAX_SAFE_INT_DBL || d < -MAX_SAFE_INT_DBL) {
    throw DREAL_RUNTIME_ERROR("Input integer {} is too large", s);
  }
  return static_cast<int64_t>(d);
}

double strtod_checked(const char *s) {
  char *endptr;
  double result = strtod(s, &endptr);
  if (result == HUGE_VAL || result == -HUGE_VAL) {
    throw DREAL_RUNTIME_ERROR("Input real {} is too large", s);
  } else if (*endptr || endptr == s) {
    throw DREAL_RUNTIME_ERROR("Input real {} is invalid", s);
  }
  return result;
}
}  // namespace dreal
