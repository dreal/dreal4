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

#include <utility>

#include "dreal/util/box.h"
#include "dreal/util/dynamic_bitset.h"

namespace dreal {

/// Finds the dimension with the maximum diameter in a @p box. It only
/// consider the dimensions enabled in @p active_set.
///
/// @returns a pair of (max dimension, variable index).
std::pair<double, int> FindMaxDiam(const Box& box,
                                   const DynamicBitset& active_set);

/// Finds the largest dimension in `active_set` and partitions `box`
/// into two sub-boxes by branching on the chosen dimension. It
/// traverses only the variables enabled by @p active_set, to find a
/// branching dimension.
///
/// @param[in] box The box to branch.
/// @param[in] active_set A subset of dimensions of the input box that is active
///                       in the given constraints.
/// @param[out] left The left sub-box.
/// @param[out] right The right sub-box.
///
/// @returns the branching dimension if found, otherwise returns -1.
int BranchLargestFirst(const Box& box, const DynamicBitset& active_set,
                       Box* left, Box* right);

}  // namespace dreal
