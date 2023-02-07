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

#include <memory>
#include <set>
#include <unordered_map>
#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/solver/config.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/solver/icp.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/optional.h"

namespace dreal {

/// Theory solver for nonlinear theory over the Reals.
class TheorySolver {
 public:
  TheorySolver() = delete;
  explicit TheorySolver(const Config& config);

  /// Checks consistency. Returns true if there is a satisfying
  /// assignment. Otherwise, return false.
  bool CheckSat(const Box& box, const std::vector<Formula>& assertions);

  /// Gets a satisfying Model.
  const Box& GetModel() const;

  /// Gets a list of used constraints.
  const std::set<Formula>& GetExplanation() const;

  optional<Contractor> BuildContractor(const std::vector<Formula>& assertions,
                                       ContractorStatus* contractor_status);

 private:
  // Builds a contractor using @p box and @p assertions. It returns
  // nullopt if it detects an empty box while building a contractor.
  //
  // @note This method updates @p box as it calls FilterAssertion
  // function.
  std::vector<FormulaEvaluator> BuildFormulaEvaluator(
      const std::vector<Formula>& assertions);

  const Config& config_;
  std::unique_ptr<Icp> icp_;
  Box model_;
  std::set<Formula> explanation_;
  std::unordered_map<Formula, Contractor> contractor_cache_;
  std::unordered_map<Formula, FormulaEvaluator> formula_evaluator_cache_;
};

}  // namespace dreal
