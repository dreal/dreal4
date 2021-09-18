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

#include <ostream>
#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_cell.h"
#include "dreal/util/box.h"

namespace dreal {

/// Fixpoint contractor using the worklist algorithm: apply C₁, ..., Cₙ
/// until it reaches a fixpoint or it satisfies a given termination
/// condition.
class ContractorWorklistFixpoint : public ContractorCell {
 public:
  /// Deletes default constructor.
  ContractorWorklistFixpoint() = delete;

  /// Constructs a fixpoint contractor with a termination condition
  /// (Box × Box → Bool) and a sequence of Contractors {C₁, ..., Cₙ}.
  ContractorWorklistFixpoint(TerminationCondition term_cond,
                             std::vector<Contractor> contractors,
                             const Config& config);

  /// Deleted copy constructor.
  ContractorWorklistFixpoint(const ContractorWorklistFixpoint&) = delete;

  /// Deleted move constructor.
  ContractorWorklistFixpoint(ContractorWorklistFixpoint&&) = delete;

  /// Deleted copy assign operator.
  ContractorWorklistFixpoint& operator=(const ContractorWorklistFixpoint&) =
      delete;

  /// Deleted move assign operator.
  ContractorWorklistFixpoint& operator=(ContractorWorklistFixpoint&&) = delete;

  /// Default destructor.
  ~ContractorWorklistFixpoint() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

 private:
  // Stop the fixed-point iteration if term_cond(old_box, new_box) is true.
  const TerminationCondition term_cond_;
  std::vector<Contractor> contractors_;

  // input_to_contractors_[i] is the set of contractors whose input
  // includes the i-th variable. That is, `input_to_contractors_[i][j]
  // = true` indicates that if i-th dimension of the current box
  // changes in a pruning operation, we need to run contractors_[j]
  // because i ∈ contractors_[j].input(). This map is constructed in
  // the constructor.
  std::vector<DynamicBitset> input_to_contractors_;
};

}  // namespace dreal
