#pragma once

#include <ostream>
#include <string>

#include "dreal/symbolic/symbolic.h"

namespace dreal {

// TODO(soonho): Extend this.
enum class Sort {
  Binary,
  Bool,
  Int,
  Real,
};

Sort ParseSort(const std::string& s);

std::ostream& operator<<(std::ostream& os, const Sort& sort);

Variable::Type SortToType(Sort sort);

}  // namespace dreal
