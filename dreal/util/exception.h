#pragma once

#include <fmt/format.h>

namespace dreal {
#include <stdexcept>

#define DREAL_RUNTIME_ERROR(message) \
  std::runtime_error(fmt::format("{}:{} {}.", message, __FILE__, __LINE__))

#define DREAL_UNREACHABLE() \
  throw DREAL_RUNTIME_ERROR("Should not be reachable.")  // LCOV_EXCL_LINE

}  // namespace dreal
