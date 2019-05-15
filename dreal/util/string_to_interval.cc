#include "dreal/util/string_to_interval.h"

#include "dreal/util/rounding_mode_guard.h"

namespace dreal {

using std::stod;
using std::string;

Box::Interval StringToInterval(const string& s) {
  RoundingModeGuard guard(FE_UPWARD);
  const double ub{stod(s)};
  double lb{};
  if (s[0] == '-') {
    lb = -stod(s.substr(1));
  } else {
    lb = -stod("-" + s);
  }
  return Box::Interval{lb, ub};
}

}  // namespace dreal
