#pragma once

#include <string>

#include "dreal/util/box.h"

namespace dreal {
/// Convert a string @p s into an interval `[lb, ub]` where `lb` is a
/// parsed result of @p s with FE_DOWNWARD round-mode and `ub` is a
/// parsed result of @p s with FE_UPWARD round-mode.
///
/// @throw if @p s does not represent a double number. (see std::stod)
///
/// @note This function assumes that std::stod implementation honors
/// the current round-mode. There are old versions of Visual C++ and
/// GLIBC where this assumption does not hold.  See
/// http://www.exploringbinary.com/visual-c-plus-plus-and-glibc-strtod-ignore-rounding-mode
/// for more information.
Box::Interval StringToInterval(const std::string& s);
}  // namespace dreal
