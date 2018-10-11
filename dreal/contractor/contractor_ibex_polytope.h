#pragma once

#include <memory>
#include <ostream>
#include <vector>

#include "./ibex.h"

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_cell.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

// Custom deleter for ibex::ExprCtr. It deletes the internal
// ibex::ExprNode while keeping the ExprSymbols intact. Note that the
// ExprSymbols will be deleted separately in
// ~ContractorIbexPolytope().
struct ExprCtrDeleter {
  void operator()(const ibex::ExprCtr* const p) const {
    if (p) {
      ibex::cleanup(p->e, false);
      delete p;
    }
  }
};

class ContractorIbexPolytope : public ContractorCell {
 public:
  /// Constructs IbexPolytope contractor using @p f and @p vars.
  ContractorIbexPolytope(std::vector<Formula> formulas, const Box& box,
                         const Config& config);

  /// Deleted copy constructor.
  ContractorIbexPolytope(const ContractorIbexPolytope&) = delete;

  /// Deleted move constructor.
  ContractorIbexPolytope(ContractorIbexPolytope&&) = delete;

  /// Deleted copy assign operator.
  ContractorIbexPolytope& operator=(const ContractorIbexPolytope&) = delete;

  /// Deleted move assign operator.
  ContractorIbexPolytope& operator=(ContractorIbexPolytope&&) = delete;

  /// Default destructor.
  ~ContractorIbexPolytope() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

 private:
  const std::vector<Formula> formulas_;

  IbexConverter ibex_converter_;
  std::unique_ptr<ibex::SystemFactory> system_factory_;
  std::unique_ptr<ibex::System> system_;
  std::unique_ptr<ibex::LinearizerCombo> linear_relax_combo_;
  std::unique_ptr<ibex::CtcPolytopeHull> ctc_;
  std::vector<std::unique_ptr<const ibex::ExprCtr, ExprCtrDeleter>> expr_ctrs_;

  // Temporary storage to store an old interval vector.
  mutable Box::IntervalVector old_iv_;
};

}  // namespace dreal
