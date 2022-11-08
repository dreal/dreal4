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

#include <functional>
#include <ostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_cell.h"
#include "dreal/util/box.h"

namespace dreal {

/// Sampling contractor:
/// Use sampling method to find a SAT solution directly in the box
class ContractorSampling : public ContractorCell {
 public:
  /// Deletes default constructor.
  ContractorSampling() = delete;

  /// Constructs a sampling contractor from a vector of formulas.
  ContractorSampling(const std::vector<Formula> input_formulas, const Box& box,
                     const Config& config);

  /// Deleted copy constructor.
  ContractorSampling(const ContractorSampling&) = delete;

  /// Deleted move constructor.
  ContractorSampling(ContractorSampling&&) = delete;

  /// Deleted copy assign operator.
  ContractorSampling& operator=(const ContractorSampling&) = delete;

  /// Deleted move assign operator.
  ContractorSampling& operator=(ContractorSampling&&) = delete;

  /// Default destructor.
  ~ContractorSampling() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

 private:
  std::vector<Formula> formulas;
};

}  // namespace dreal
