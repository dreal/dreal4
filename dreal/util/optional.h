#pragma once

#include "dreal/util/optional.hpp"

namespace dreal {
template <typename T>
using optional = tl::optional<T>;
constexpr auto nullopt = tl::nullopt;
}  // namespace dreal
