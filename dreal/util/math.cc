#include "dreal/util/math.h"

#include <cmath>

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
}  // namespace dreal
