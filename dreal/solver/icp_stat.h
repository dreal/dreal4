#pragma once

#include "dreal/util/stat.h"
#include "dreal/util/timer.h"

namespace dreal {

/// A class to show statistics information at destruction. We have a
/// static instance in Icp::CheckSat() to keep track of the numbers of
/// branching and pruning operations.
class IcpStat : public Stat {
 public:
  explicit IcpStat(const bool enabled) : Stat{enabled} {}
  IcpStat(const IcpStat&) = default;
  IcpStat(IcpStat&&) = default;
  IcpStat& operator=(const IcpStat&) = default;
  IcpStat& operator=(IcpStat&&) = default;
  ~IcpStat() override;

  int num_branch_{0};
  int num_prune_{0};
  Timer timer_branch_;
  Timer timer_prune_;
  Timer timer_eval_;
};
}  // namespace dreal
