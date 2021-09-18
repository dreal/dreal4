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
