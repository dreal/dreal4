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
