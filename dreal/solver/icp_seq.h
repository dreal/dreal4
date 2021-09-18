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

#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_status.h"
#include "dreal/solver/config.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/solver/icp.h"

namespace dreal {

/// Class for ICP (Interval Constraint Propagation) algorithm.
class IcpSeq : public Icp {
 public:
  /// Constructs an IcpSeq based on @p config.
  explicit IcpSeq(const Config& config);

  bool CheckSat(const Contractor& contractor,
                const std::vector<FormulaEvaluator>& formula_evaluators,
                ContractorStatus* cs) override;

 private:
  // If `stack_left_box_first_` is true, we add the left box from the
  // branching operation to the `stack`. Otherwise, we add the right
  // box first.
  bool stack_left_box_first_{false};
};

}  // namespace dreal
