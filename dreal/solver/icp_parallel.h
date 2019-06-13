#pragma once

#include <future>
#include <vector>

#include "ThreadPool/ThreadPool.h"

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_status.h"
#include "dreal/solver/config.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/solver/icp.h"

namespace dreal {

/// Class for Parallel ICP (Interval Constraint Propagation) algorithm.
class IcpParallel : public Icp {
 public:
  /// Constructs an IcpParallel based on @p config.
  explicit IcpParallel(const Config& config);

  bool CheckSat(const Contractor& contractor,
                const std::vector<FormulaEvaluator>& formula_evaluators,
                ContractorStatus* cs) override;

 private:
  ThreadPool pool_;

  std::vector<std::future<void>> results_;
  std::vector<ContractorStatus> status_vector_;
};

}  // namespace dreal
