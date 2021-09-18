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

#include <set>
#include <vector>

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/dynamic_bitset.h"

namespace dreal {

/// Contractor status
class ContractorStatus {
 public:
  ContractorStatus() = delete;

  /// Constructs a contractor status with @p box and @p branching_point.
  explicit ContractorStatus(Box box, int branching_point = -1);

  /// Returns a const reference of the embedded box.
  const Box& box() const;

  /// Returns a mutable reference of the embedded box.
  Box& mutable_box();

  /// Returns the branching_point.
  int branching_point() const;

  /// Returns a mutable reference of the branching_point.
  int& mutable_branching_point();

  /// Returns a const reference of the output field.
  const DynamicBitset& output() const;

  /// Returns a mutable reference of the output field.
  DynamicBitset& mutable_output();

  /// Returns explanation, a list of formula responsible for the unsat.
  std::set<Formula> Explanation() const;

  /// Add a formula @p f into the used constraints.
  void AddUsedConstraint(const Formula& f);

  /// Add a formula @p formulas into the used constraints.
  void AddUsedConstraint(const std::vector<Formula>& formulas);

  /// Add a variable @p var which is directly responsible for the unsat.
  void AddUnsatWitness(const Variable& var);

  /// Updates the contractor status by taking join with @p contractor_status.
  ///
  /// @pre The boxes of this and @p contractor_status have the same variables
  /// vector.
  ContractorStatus& InplaceJoin(const ContractorStatus& contractor_status);

 private:
  // The current box to prune. Most of contractors are updating
  // this member.
  Box box_;

  // If the nested box is obtained from a branching operation, this field
  // records the dimension (variable) where the branching occurred. The default
  // value is -1, which indicates that the box is not obtained by a branching.
  //
  // This field is used in worklist-fixpoint contractor.
  int branching_point_{-1};

  // "output_[i] == 1" means that the value of the i-th variable is
  // changed after running the contractor.
  DynamicBitset output_;

  // A set of constraints used during pruning processes. This is an
  // over-approximation of an explanation.
  std::set<Formula> used_constraints_;

  // A set of variables directly responsible for the unsat result. This
  // is used to generate an explanation.
  Variables unsat_witness_;
};

/// Returns a join of @p contractor_status1 and @p contractor_status2.
///
/// @pre The boxes of the two ContractorStatus should have the same variables
/// vector.
ContractorStatus Join(ContractorStatus contractor_status1,
                      const ContractorStatus& contractor_status2);

}  // namespace dreal
