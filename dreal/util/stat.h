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
