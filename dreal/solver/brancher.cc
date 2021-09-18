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
#include "dreal/solver/brancher.h"

#include "dreal/util/assert.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::make_pair;
using std::pair;

pair<double, int> FindMaxDiam(const Box& box, const DynamicBitset& active_set) {
  DREAL_ASSERT(!active_set.none());
  double max_diam{0.0};
  int max_diam_idx{-1};
  DynamicBitset::size_type idx = active_set.find_first();
  while (idx != DynamicBitset::npos) {
    const Box::Interval& iv_i{box[idx]};
    const double diam_i{iv_i.diam()};
    if (diam_i > max_diam && iv_i.is_bisectable()) {
      max_diam = diam_i;
      max_diam_idx = idx;
    }
    idx = active_set.find_next(idx);
  }
  return make_pair(max_diam, max_diam_idx);
}

int BranchLargestFirst(const Box& box, const DynamicBitset& active_set,
                       Box* const left, Box* const right) {
  DREAL_ASSERT(!active_set.none());

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
        box, box.variable(branching_dim), *left, *right);
    return branching_dim;
  }
  return -1;
}
}  // namespace dreal
