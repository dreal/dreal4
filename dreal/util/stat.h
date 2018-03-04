#pragma once

namespace dreal {

/// Base class for statistics.
class Stat {
 public:
  explicit Stat(bool enabled) : enabled_{enabled} {}
  Stat(const Stat&) = default;
  Stat(Stat&&) = default;
  Stat& operator=(const Stat&) = default;
  Stat& operator=(Stat&&) = default;
  virtual ~Stat() = default;

  /// Returns true if the logging is enabled. Normally, this is
  /// checked in the destructor of a derived class and determine
  /// whether to log or not.
  bool enabled() { return enabled_; }

 private:
  bool enabled_{false};
};
}  // namespace dreal
