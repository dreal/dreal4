#include "dreal/contractor/contractor_ibex_polytope.h"

#include <memory>
#include <sstream>
#include <utility>
#include <vector>

#include "dreal/util/logging.h"
#include "dreal/util/math.h"

using std::make_unique;
using std::move;
using std::ostream;
using std::ostringstream;
using std::unique_ptr;
using std::vector;

namespace dreal {

namespace {

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
}  // namespace

//---------------------------------------
// Implementation of ContractorIbexPolytope
//---------------------------------------
ContractorIbexPolytope::ContractorIbexPolytope(vector<Formula> formulas,
                                               const Box& box)
    : ContractorCell{Contractor::Kind::IBEX_POLYTOPE,
                     ibex::BitSet::empty(box.size())},
      formulas_{move(formulas)},
      ibex_converter_{box} {
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
    static Box::IntervalVector old_iv{iv};
    old_iv = iv;
    DREAL_LOG_TRACE("ContractorIbexPolytope::Prune");
    ctc_->contract(iv);
    bool changed{false};
    // Update output.
    if (iv.is_empty()) {
      changed = true;
      cs->mutable_output().fill(0, cs->box().size() - 1);
    } else {
      for (int i = 0; i < old_iv.size(); ++i) {
        if (old_iv[i] != iv[i]) {
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
        DisplayDiff(oss, cs->box().variables(), old_iv,
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
