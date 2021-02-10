#pragma once

#include <iostream>
#include <limits>

namespace dreal {

/// Sets the decimal precision to be used to format floating-point
/// values on output operations. Restores the old precision when this guard is
/// destroyed.
class PrecisionGuard final {
 public:
  explicit PrecisionGuard(
      std::ostream* os_,
      std::streamsize precision = std::numeric_limits<double>::max_digits10);

  ~PrecisionGuard();

  PrecisionGuard(const PrecisionGuard&) = delete;
  void operator=(const PrecisionGuard&) = delete;
  PrecisionGuard(PrecisionGuard&&) = delete;
  void operator=(PrecisionGuard&&) = delete;

 private:
  std::ostream* os_{nullptr};
  std::streamsize old_precision_;
};
}  // namespace dreal
