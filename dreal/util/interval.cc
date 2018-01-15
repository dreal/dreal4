#include "dreal/util/interval.h"

#include <cmath>
#include <limits>

namespace dreal {

using std::nextafter;
using std::numeric_limits;

Box::Interval BloatPoint(const double c) {
  const double lb{nextafter(c, -numeric_limits<double>::infinity())};
  const double ub{nextafter(c, +numeric_limits<double>::infinity())};
  return Box::Interval(lb, ub);
}
}  // namespace dreal
