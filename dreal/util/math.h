#pragma once

namespace dreal {
/// Returns true if @p v is represented by `int`.
bool is_integer(double v);

/// Converts @p v of long to int.
/// @throw std::runtime_error if this conversion result in a loss of precision.
// NOLINTNEXTLINE(runtime/int)
int convert_long_to_int(long v);

/// Converts @p v of long to double.
/// @throw std::runtime_error if this conversion result in a loss of precision.
// NOLINTNEXTLINE(runtime/int)
double convert_long_to_double(long v);

}  // namespace dreal
