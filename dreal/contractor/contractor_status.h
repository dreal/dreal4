#pragma once

#include <set>
#include <unordered_set>
#include <vector>

#include "./ibex.h"

#include "dreal/util/box.h"
#include "dreal/util/symbolic.h"

namespace dreal {

/// TODO(soonho): Add documentation.
class ContractorStatus {
 public:
  ContractorStatus() = delete;

  /// Constructs a contractor status with @p box.
  explicit ContractorStatus(Box box);

  /// Returns the embedded box.
  const Box& box() const;
  /// Returns the embedded box.
  Box& get_mutable_box();

  /// Returns the output.
  const ibex::BitSet& output() const;
  /// Returns the output.
  ibex::BitSet& get_mutable_output();

  /// Returns the used constraints.
  const std::set<Formula>& used_constraints() const;
  /// Returns the used constraints.
  std::set<Formula>& get_mutable_used_constraints();

  /// Add a formula @p f into the used constraints.
  void AddUsedConstraint(Formula f);

  /// Add a formula @p formulas into the used constraints.
  void AddUsedConstraint(const std::vector<Formula>& formulas);

  /// Updates the contractor status by taking join with @p contractor_status.
  ///
  /// @pre The boxes of this and @p contractor_status have the same variables
  /// vector.
  ContractorStatus& InplaceJoin(const ContractorStatus& contractor_status);

 private:
  /// The current box to prune. Most of contractors are updating
  /// this member.
  Box box_;

  /// Some of contractors return a set of boxes in their pruning
  /// processes. The first one is saved in m_box, the rest will be
  /// saved in m_box_stack.
  /// std::vector<Box> box_stack_;

  // "output_[i] == 1" means that the value of the i-th variable is
  // changed after running the contractor.
  ibex::BitSet output_;

  std::set<Formula> used_constraints_;
};

/// Returns a join of @p contractor_status1 and @p contractor_status2.
///
/// @pre The boxes of the two ContractorStatus should have the same variables
/// vector.
ContractorStatus Join(ContractorStatus contractor_status1,
                      const ContractorStatus& contractor_status2);

}  // namespace dreal
