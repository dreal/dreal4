#pragma once

#include <memory>
#include <ostream>

#include "./ibex.h"

#include "dreal/contractor/contractor_cell.h"
#include "dreal/contractor/contractor_status.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

/// Contractor class wrapping IBEX's forward/backward contractor.
class ContractorIbexFwdbwd : public ContractorCell {
 public:
  /// Deleted default constructor.
  ContractorIbexFwdbwd() = delete;

  /// Constructs IbexFwdbwd contractor using @p f and @p box.
  ContractorIbexFwdbwd(Formula f, const Box& box, const Config& config);

  /// Deleted copy constructor.
  ContractorIbexFwdbwd(const ContractorIbexFwdbwd&) = delete;

  /// Deleted move constructor.
  ContractorIbexFwdbwd(ContractorIbexFwdbwd&&) = delete;

  /// Deleted copy assign operator.
  ContractorIbexFwdbwd& operator=(const ContractorIbexFwdbwd&) = delete;

  /// Deleted move assign operator.
  ContractorIbexFwdbwd& operator=(ContractorIbexFwdbwd&&) = delete;

  ~ContractorIbexFwdbwd() override = default;

  void Prune(ContractorStatus* cs) const override;

  std::ostream& display(std::ostream& os) const override;

  /// Returns true if it has no internal ibex contractor.
  bool is_dummy() const;

 private:
  const Formula f_;
  bool is_dummy_{false};
  IbexConverter ibex_converter_;
  std::unique_ptr<const ibex::ExprCtr> expr_ctr_;
  std::unique_ptr<ibex::NumConstraint> num_ctr_;
};

}  // namespace dreal
