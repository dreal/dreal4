#pragma once

#include <ostream>
#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_cell.h"

namespace dreal {

/// Join contractor.
/// (C₁ ∨ ... ∨ Cₙ)(b) = C₁(b) ∨ ... ∨ Cₙ(b).
class ContractorJoin : public ContractorCell {
 public:
  /// Deletes default constructor.
  ContractorJoin() = delete;

  /// Constructs a join contractor from a {C₁, ..., Cₙ}.
  ContractorJoin(std::vector<Contractor> contractors, const Config& config);

  /// Deleted copy constructor.
  ContractorJoin(const ContractorJoin&) = delete;

  /// Deleted move constructor.
  ContractorJoin(ContractorJoin&&) = delete;

  /// Deleted copy assign operator.
  ContractorJoin& operator=(const ContractorJoin&) = delete;

  /// Deleted move assign operator.
  ContractorJoin& operator=(ContractorJoin&&) = delete;

  /// Default destructor.
  ~ContractorJoin() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

 private:
  std::vector<Contractor> contractors_;
};
}  // namespace dreal
