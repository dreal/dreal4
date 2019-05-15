#include "dreal/solver/branch.h"

#include "dreal/util/assert.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::make_pair;
using std::pair;
using std::vector;

pair<double, int> FindMaxDiam(const Box& box, const ibex::BitSet& bitset) {
  DREAL_ASSERT(!bitset.empty());
  double max_diam{0.0};
  int max_diam_idx{-1};
  for (int i = 0, idx = bitset.min(); i < bitset.size();
       ++i, idx = bitset.next(idx)) {
    const Box::Interval& iv_i{box[idx]};
    const double diam_i{iv_i.diam()};
    if (diam_i > max_diam && iv_i.is_bisectable()) {
      max_diam = diam_i;
      max_diam_idx = idx;
    }
  }
  return make_pair(max_diam, max_diam_idx);
}

bool Branch(const Box& box, const ibex::BitSet& bitset,
            const bool stack_left_box_first,
            vector<pair<Box, int>>* const stack) {
  DREAL_ASSERT(!bitset.empty());

  // TODO(soonho): For now, we fixated the branching heuristics.
  // Generalize it later.
  const pair<double, int> max_diam_and_idx{FindMaxDiam(box, bitset)};
  const int branching_point{max_diam_and_idx.second};
  if (branching_point >= 0) {
    const pair<Box, Box> bisected_boxes{box.bisect(branching_point)};
    if (stack_left_box_first) {
      stack->emplace_back(bisected_boxes.first, branching_point);
      stack->emplace_back(bisected_boxes.second, branching_point);
      DREAL_LOG_DEBUG(
          "Branch {}\n"
          "on {}\n"
          "Box1=\n{}\n"
          "Box2=\n{}",
          box, box.variable(branching_point), bisected_boxes.first,
          bisected_boxes.second);
    } else {
      stack->emplace_back(bisected_boxes.second, branching_point);
      stack->emplace_back(bisected_boxes.first, branching_point);
      DREAL_LOG_DEBUG(
          "Branch {}\n"
          "on {}\n"
          "Box1=\n{}\n"
          "Box2=\n{}",
          box, box.variable(branching_point), bisected_boxes.second,
          bisected_boxes.first);
    }
    return true;
  }
  // Fail to find a branching point.
  return false;
}
}  // namespace dreal
