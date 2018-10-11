#include "dreal/contractor/contractor_ibex_polytope.h"

#include <sstream>
#include <utility>

#include "dreal/util/logging.h"
#include "dreal/util/math.h"

using std::make_unique;
using std::move;
using std::ostream;
using std::ostringstream;
using std::unique_ptr;
using std::vector;

namespace dreal {

//---------------------------------------
// Implementation of ContractorIbexPolytope
//---------------------------------------
ContractorIbexPolytope::ContractorIbexPolytope(vector<Formula> formulas,
                                               const Box& box,
                                               const Config& config)
    : ContractorCell{Contractor::Kind::IBEX_POLYTOPE,
                     ibex::BitSet::empty(box.size()), config},
      formulas_{move(formulas)},
      ibex_converter_{box},
      old_iv_{1 /* Will be overwritten anyway */} {
  DREAL_LOG_DEBUG("ContractorIbexPolytope::ContractorIbexPolytope");

  // Build SystemFactory. Add variables and constraints.
  system_factory_ = make_unique<ibex::SystemFactory>();
  system_factory_->add_var(ibex_converter_.variables());
  for (const Formula& f : formulas_) {
    if (!is_forall(f)) {
      unique_ptr<const ibex::ExprCtr, ExprCtrDeleter> expr_ctr{
          ibex_converter_.Convert(f)};
      if (expr_ctr) {
        system_factory_->add_ctr(*expr_ctr);
        // We need to postpone the destruction of expr_ctr as it is
        // still used inside of system_factory_.
        expr_ctrs_.push_back(std::move(expr_ctr));
      }
    }
  }
  ibex_converter_.set_need_to_delete_variables(true);

  // Build System.
  system_ = make_unique<ibex::System>(*system_factory_);
  if (system_->nb_ctr == 0) {
    return;
  }

  // Build Polytope contractor from system.
  linear_relax_combo_ = make_unique<ibex::LinearizerCombo>(
      *system_, ibex::LinearizerCombo::XNEWTON);
  ctc_ = make_unique<ibex::CtcPolytopeHull>(*linear_relax_combo_);

  // Build input.
  ibex::BitSet& input{mutable_input()};
  for (const Formula& f : formulas_) {
    for (const Variable& var : f.GetFreeVariables()) {
      input.add(box.index(var));
    }
  }
}

void ContractorIbexPolytope::Prune(ContractorStatus* cs) const {
  if (ctc_) {
    Box::IntervalVector& iv{cs->mutable_box().mutable_interval_vector()};
    old_iv_ = iv;
    DREAL_LOG_TRACE("ContractorIbexPolytope::Prune");
    ctc_->contract(iv);
    bool changed{false};
    // Update output.
    if (iv.is_empty()) {
      changed = true;
      cs->mutable_output().fill(0, cs->box().size() - 1);
    } else {
      for (int i = 0; i < old_iv_.size(); ++i) {
        if (old_iv_[i] != iv[i]) {
          cs->mutable_output().add(i);
          changed = true;
        }
      }
    }
    // Update used constraints.
    if (changed) {
      cs->AddUsedConstraint(formulas_);
      if (DREAL_LOG_TRACE_ENABLED) {
        ostringstream oss;
        DisplayDiff(oss, cs->box().variables(), old_iv_,
                    cs->box().interval_vector());
        DREAL_LOG_TRACE("Changed\n{}", oss.str());
      }
    } else {
      DREAL_LOG_TRACE("NO CHANGE");
    }
  }
}

ostream& ContractorIbexPolytope::display(ostream& os) const {
  os << "IbexPolytope(";
  for (const Formula& f : formulas_) {
    os << f << ";";
  }
  os << ")";
  return os;
}

}  // namespace dreal
