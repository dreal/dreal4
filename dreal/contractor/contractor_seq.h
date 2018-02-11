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
  ContractorSeq(std::vector<Contractor> contractors, const Config& config);

  /// Deleted copy constructor.
  ContractorSeq(const ContractorSeq&) = delete;

  /// Deleted move constructor.
  ContractorSeq(ContractorSeq&&) = delete;

  /// Deleted copy assign operator.
  ContractorSeq& operator=(const ContractorSeq&) = delete;

  /// Deleted move assign operator.
  ContractorSeq& operator=(ContractorSeq&&) = delete;

  /// Default destructor.
  ~ContractorSeq() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

  const std::vector<Contractor>& contractors() const;

 private:
  std::vector<Contractor> contractors_;
};
}  // namespace dreal
