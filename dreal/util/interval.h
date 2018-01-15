#pragma once

#include "dreal/util/box.h"

namespace dreal {

/// Expands a point value @p c into an interval `[prev_c, next_c]`
/// where `prev_c` is the largest machine-representable floating-point
/// number which is smaller than c and `next_c` is the smallest
/// machine-representable floating-point number which is larger than
/// c.
///
/// @note When c is +∞ (resp. -∞), this function returns [DBL_MAX, +∞]
/// (resp. -[-∞, DBL_MAX]).
Box::Interval BloatPoint(double c);

}  // namespace dreal
