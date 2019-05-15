#pragma once

#include <utility>
#include <vector>

#include "dreal/util/box.h"

namespace dreal {

/// Finds the dimension with the maximum diameter in a @p box. It only
/// consider the dimensions enabled in @p bitset.
///
/// @returns a pair of (max dimension, variable index).
std::pair<double, int> FindMaxDiam(const Box& box, const ibex::BitSet& bitset);

/// Partitions @p box into two sub-boxes and add them into the @p
/// stack. It traverses only the variables enabled by @p bitset, to find a
/// branching dimension.
///
/// @returns true if it finds a branching dimension and adds boxes to the @p
/// stack.
/// @returns false if it fails to find a branching dimension.
bool Branch(const Box& box, const ibex::BitSet& bitset,
            bool stack_left_box_first, std::vector<std::pair<Box, int>>* stack);

}  // namespace dreal
