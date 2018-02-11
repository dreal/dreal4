#pragma once

#include "dreal/contractor/contractor_cell.h"

namespace dreal {

class ContractorId : public ContractorCell {
 public:
  /// Constructs ID contractor.
  explicit ContractorId(const Config& config);

  /// Deleted copy constructor.
  ContractorId(const ContractorId&) = delete;

  /// Deleted move constructor.
  ContractorId(ContractorId&&) = delete;

  /// Deleted copy assign operator.
  ContractorId& operator=(const ContractorId&) = delete;

  /// Deleted move assign operator.
  ContractorId& operator=(ContractorId&&) = delete;

  /// Default destructor.
  ~ContractorId() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;
};
}  // namespace dreal
