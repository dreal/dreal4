#include "dreal/util/math.h"

#include <cmath>
#include <climits>

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

long strtol_checked(const char *s) {
  char *endptr;
  long result = strtol(s, &endptr, 10);  // specified to return `long`
  if (result == LONG_MAX || result == LONG_MIN) {
    throw DREAL_RUNTIME_ERROR("Input integer {} is too large", s);
  } else if (*endptr || endptr == s) {
    throw DREAL_RUNTIME_ERROR("Input integer {} is invalid", s);
  }
  return result;
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
