#include "dreal/util/string_to_interval.h"

#include <cfenv>

namespace dreal {

using std::fegetround;
using std::fesetround;
using std::stod;
using std::string;

namespace {
class RoundModeGuard {
 public:
  /// Saves the current round-mode and switch to @p new_round.
  explicit RoundModeGuard(int new_round) : round_mode_{fegetround()} {
    fesetround(new_round);
  }

  /// Deleted Copy-constructor.
  RoundModeGuard(const RoundModeGuard&) = delete;

  /// Deleted Move-constructor.
  RoundModeGuard(RoundModeGuard&&) = delete;

  /// Deleted Copy-assignment.
  RoundModeGuard& operator=(const RoundModeGuard&) = delete;

  /// Deleted Move-assignment.
  RoundModeGuard& operator=(RoundModeGuard&&) = delete;

  /// Destructor. Restore the saved round-mode.
  ~RoundModeGuard() { fesetround(round_mode_); }

 private:
  /// Saved round-mode at the construction.
  const int round_mode_{};
};
}  // namespace

Box::Interval StringToInterval(const string& s) {
  RoundModeGuard guard(FE_UPWARD);
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
