#pragma once
#include <limits>
#include <cstdint>

namespace dreal {
// Returns true if @p v is represented by `int`.
bool is_integer(double v);
// Like `strtol()` but it throws an exception if the number is too large
int64_t strtol_checked(const char *s);
// Like `strtod()` but it throws an exception if the number is too large
double strtod_checked(const char *s);
}  // namespace dreal
