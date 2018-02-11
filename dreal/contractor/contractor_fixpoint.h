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
  std::vector<Contractor> contractors_;

  // Temporary storage for old interval vector.
  mutable Box::IntervalVector old_iv_;
};

}  // namespace dreal
