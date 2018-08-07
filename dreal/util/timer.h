#pragma once

#include <chrono>
#include <iostream>
#include <type_traits>

namespace dreal {

/// Simple timer class to profile performance.
class Timer {
 public:
  // Use high_resolution clock if it's steady. Otherwise use steady_clock.
  using clock = std::conditional<std::chrono::high_resolution_clock::is_steady,
                                 std::chrono::high_resolution_clock,
                                 std::chrono::steady_clock>::type;
  Timer();

  /// Starts the timer.
  void start();

  /// Pauses the timer.
  void pause();

  /// Resumes the timer.
  void resume();

  /// Checks if the timer is running.
  bool is_running() const;

  /// Returns the elapsed time.
  clock::duration elapsed() const;

 private:
  // Whether the timer is running or not.
  bool running_{false};

  // Last time_point when the timer is started or resumed.
  clock::time_point last_start_{};

  // Elapsed time so far. This doesn't include the current fragment if
  // it is running.
  clock::duration elapsed_{};
};

std::ostream& operator<<(std::ostream& os, const Timer& timer);
}  // namespace dreal
