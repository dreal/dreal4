#pragma once

#include <cfenv>

namespace dreal {

class RoundingModeGuard {
 public:
  /// Saves the current rounding-mode and switch to @p new_round.
  explicit RoundingModeGuard(int new_round) : round_mode_{fegetround()} {
    fesetround(new_round);
  }

  /// Deleted Copy-constructor.
  RoundingModeGuard(const RoundingModeGuard&) = delete;

  /// Deleted Move-constructor.
  RoundingModeGuard(RoundingModeGuard&&) = delete;

  /// Deleted Copy-assignment.
  RoundingModeGuard& operator=(const RoundingModeGuard&) = delete;

  /// Deleted Move-assignment.
  RoundingModeGuard& operator=(RoundingModeGuard&&) = delete;

  /// Destructor. Restore the saved rounding-mode.
  ~RoundingModeGuard() { fesetround(round_mode_); }

 private:
  /// Saved rounding-mode at the construction.
  const int round_mode_{};
};
}  // namespace dreal
