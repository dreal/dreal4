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

#include <atomic>

namespace dreal {

/// Base class for statistics.
class Stat {
 public:
  explicit Stat(bool enabled) : enabled_{enabled} {}
  Stat(const Stat&) = default;
  Stat(Stat&&) = default;
  Stat& operator=(const Stat&) = delete;
  Stat& operator=(Stat&&) = delete;
  virtual ~Stat() = default;

  /// Returns true if the logging is enabled. Normally, this is
  /// checked in the destructor of a derived class and determine
  /// whether to log or not.
  bool enabled() const { return enabled_; }

 protected:
  template <typename T>
  void increase(std::atomic<T>* v) {
    if (enabled_) {
      std::atomic_fetch_add_explicit(v, 1, std::memory_order_relaxed);
    }
  }

 private:
  const bool enabled_{false};
};
}  // namespace dreal
