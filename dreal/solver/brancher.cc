#include "dreal/solver/brancher.h"

#include "dreal/util/assert.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::make_pair;
using std::pair;

pair<double, int> FindMaxDiam(const Box& box, const ibex::BitSet& active_set) {
  DREAL_ASSERT(!active_set.empty());
  double max_diam{0.0};
  int max_diam_idx{-1};
  for (auto it = active_set.begin(); it != active_set.end(); ++it) {
    const int idx = it.el;
    const Box::Interval& iv_i{box[idx]};
    const double diam_i{iv_i.diam()};
    if (diam_i > max_diam && iv_i.is_bisectable()) {
      max_diam = diam_i;
      max_diam_idx = idx;
    }
  }
  return make_pair(max_diam, max_diam_idx);
}

int BranchLargestFirst(const Box& box, const ibex::BitSet& active_set,
                       Box* const left, Box* const right) {
  DREAL_ASSERT(!active_set.empty());

  const pair<double, int> max_diam_and_idx{FindMaxDiam(box, active_set)};
  const int branching_dim{max_diam_and_idx.second};
  if (branching_dim >= 0) {
    pair<Box, Box> bisected_boxes{box.bisect(branching_dim)};
    *left = std::move(bisected_boxes.first);
    *right = std::move(bisected_boxes.second);
    DREAL_LOG_DEBUG(
        "Branch {}\n"
        "on {}\n"
        "Box1=\n{}\n"
        "Box2=\n{}",
        box, box.variable(branching_dim), bisected_boxes.first,
        bisected_boxes.second);
    return branching_dim;
  }
  return -1;
}
}  // namespace dreal
