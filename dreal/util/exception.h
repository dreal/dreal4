#pragma once

#include <fmt/format.h>

#include <stdexcept>

namespace dreal {

#define DREAL_RUNTIME_ERROR(message, ...)                        \
  std::runtime_error(fmt::format("{}:{} ", __FILE__, __LINE__) + \
                     fmt::format(message, ##__VA_ARGS__))

#define DREAL_UNREACHABLE() \
  throw DREAL_RUNTIME_ERROR("Should not be reachable.")  // LCOV_EXCL_LINE

}  // namespace dreal
