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

/// Fixpoint contractor: apply C₁, ..., Cₙ until it reaches a fixpoint
/// (technically, until it satisfies a given termination condition).
class ContractorFixpoint : public ContractorCell {
 public:
  /// Deletes default constructor.
  ContractorFixpoint() = delete;

  /// Constructs a fixpoint contractor with a termination condition
  /// (Box × Box → Bool) and a sequence of Contractors {C₁, ..., Cₙ}.
  ContractorFixpoint(TerminationCondition term_cond,
                     std::vector<Contractor> contractors, const Config& config);

  /// Deleted copy constructor.
  ContractorFixpoint(const ContractorFixpoint&) = delete;

  /// Deleted move constructor.
  ContractorFixpoint(ContractorFixpoint&&) = delete;

  /// Deleted copy assign operator.
  ContractorFixpoint& operator=(const ContractorFixpoint&) = delete;

  /// Deleted move assign operator.
  ContractorFixpoint& operator=(ContractorFixpoint&&) = delete;

  /// Default destructor.
  ~ContractorFixpoint() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

 private:
  // Stop the fixed-point iteration if term_cond(old_box, new_box) is true.
  const TerminationCondition term_cond_;
  const std::vector<Contractor> contractors_;
};

}  // namespace dreal
