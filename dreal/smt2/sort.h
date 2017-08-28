#pragma once

#include <ostream>
#include <string>

namespace dreal {

// TODO(soonho): Extend this.
enum class Sort {
  Bool,
  Int,
  Real,
};

Sort ParseSort(const std::string& s);

std::ostream& operator<<(std::ostream& os, const Sort& sort);

}  // namespace dreal
