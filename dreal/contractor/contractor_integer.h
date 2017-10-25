#pragma once

#include <vector>

#include "dreal/contractor/contractor_cell.h"
#include "dreal/util/box.h"

namespace dreal {

// Contractor for integer variables. For an integer variable `i = [lb,
// ub]`, it reduces the assignment into `[ceil(lb), floor(ub)]`.
//
// This class should be created via `make_contractor_integer` which
// handles the case where there is no integer/binary variables in a
// box.
class ContractorInteger : public ContractorCell {
 public:
  explicit ContractorInteger(const Box& box);

  /// Default destructor.
  ~ContractorInteger() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

 private:
  std::vector<int> int_indexes_;
};
}  // namespace dreal
