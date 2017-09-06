#pragma once

#include "dreal/contractor/contractor_cell.h"

namespace dreal {

class ContractorId : public ContractorCell {
 public:
  /// Constructs ID contractor.
  ContractorId();

  /// Default destructor.
  ~ContractorId() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;
};
}  // namespace dreal
