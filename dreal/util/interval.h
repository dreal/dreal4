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
