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

  /// Default destructor.
  ~ContractorFixpoint() = default;

  /// Constructs a fixpoint contractor with a termination condition
  /// (Box × Box → Bool) and a sequence of Contractors {C₁, ..., Cₙ}.
  ContractorFixpoint(TerminationCondition term_cond,
                     std::vector<Contractor> contractors);

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

 private:
  // Stop the fixed-point iteration if term_cond(old_box, new_box) is true.
  const TerminationCondition term_cond_;
  std::vector<Contractor> contractors_;
};

// /// Fixpoint contractor: Fixpoint apply C₁, ..., Cₙ.
// class ContractorFixpointDep : public ContractorCell {
//  public:
//   /// Deletes default constructor.
//   ContractorFixpointDep() = delete;

//   /// Constructs a fixpoint contractor with a termination condition
//   /// (Box × Box → Bool) and a sequence of Contractors {C₁, ..., Cₙ}.
//   ContractorFixpointDep(TerminationCondition term_cond,
//                         std::vector<Contractor> contractors);

//   void Prune(ContractorStatus* cs) const override;
//   std::ostream& display(std::ostream& os) const override;

//  private:
//   // Stop the fixed-point iteration if term_cond(old_box, new_box) is true.
//   const TerminationCondition term_cond_;
//   std::vector<Contractor> contractors_;

//   // variable_index → 2^contractor_index
//   //
//   // input_to_contractors_[i] is the set of contractors whose input
//   // include the i-th variable.
//   std::unordered_map<int, std::unordered_set<int>> input_to_contractors_;
// };

}  // namespace dreal
