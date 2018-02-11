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
  std::vector<ibex::BitSet> input_to_contractors_;

  // worklist_[i] means that i-th contractor in contractors_ needs to be
  // applied.
  mutable ibex::BitSet worklist_;
  // A temporary variable to save an old interval vector.
  mutable Box::IntervalVector old_iv_;
};

}  // namespace dreal
