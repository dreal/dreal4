#pragma once

#include <utility>

#include "dreal/util/box.h"

namespace dreal {

/// Finds the dimension with the maximum diameter in a @p box. It only
/// consider the dimensions enabled in @p active_set.
///
/// @returns a pair of (max dimension, variable index).
std::pair<double, int> FindMaxDiam(const Box& box,
                                   const ibex::BitSet& active_set);

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
int BranchLargestFirst(const Box& box, const ibex::BitSet& active_set,
                       Box* left, Box* right);

}  // namespace dreal
