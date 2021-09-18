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
