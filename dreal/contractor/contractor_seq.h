#pragma once

#include <ostream>
#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_cell.h"

namespace dreal {

/// Sequential contractor: Sequentially apply C₁, ..., Cₙ.
class ContractorSeq : public ContractorCell {
 public:
  /// Delete default constructor.
  ContractorSeq() = delete;
  /// Constructor a sequential contractor from a {C₁, ..., Cₙ}.
  explicit ContractorSeq(std::vector<Contractor> contractors);

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

  const std::vector<Contractor>& contractors() const;

 private:
  std::vector<Contractor> contractors_;
};
}  // namespace dreal
