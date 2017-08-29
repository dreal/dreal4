#pragma once

#include <memory>
#include <ostream>

#include "./ibex.h"

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_cell.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

/// Contractor class wrapping IBEX's forward/backward contractor.
class ContractorIbexFwdbwd : public ContractorCell {
 public:
  /// Deleted default constructor.
  ContractorIbexFwdbwd() = delete;

  /// Constructs IbexFwdbwd contractor using @p f and @p box.
  ContractorIbexFwdbwd(Formula f, const Box& box);
  ~ContractorIbexFwdbwd();

  void Prune(ContractorStatus* cs) const override;

  /// Evaluates the constraint using the input @box and returns the
  /// result.
  Box::Interval Evaluate(const Box& box) const;

  std::ostream& display(std::ostream& os) const override;

 private:
  const Formula f_;
  IbexConverter ibex_converter_;
  std::unique_ptr<const ibex::ExprCtr> expr_ctr_;
  std::unique_ptr<const ibex::NumConstraint> num_ctr_;
  std::unique_ptr<ibex::CtcFwdBwd> ctc_;
};

}  // namespace dreal
