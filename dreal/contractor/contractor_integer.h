#pragma once

#include <vector>

#include "dreal/contractor/contractor_cell.h"
#include "dreal/util/box.h"

namespace dreal {

class ContractorInteger : public ContractorCell {
 public:
  explicit ContractorInteger(const Box& box);
  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

 private:
  std::vector<int> int_indexes_;
};
}  // namespace dreal
