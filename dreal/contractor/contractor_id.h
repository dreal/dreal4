#pragma once

#include "dreal/contractor/contractor_cell.h"

namespace dreal {

class ContractorId : public ContractorCell {
 public:
  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;
};
}  // namespace dreal
