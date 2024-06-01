/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
#include "dreal/contractor/contractor_ibex_polytope.h"

#include <sstream>
#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/logging.h"
#include "dreal/util/math.h"

using std::make_unique;
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
    : ContractorCell{Contractor::Kind::IBEX_POLYTOPE, DynamicBitset(box.size()),
                     config},
      formulas_{std::move(formulas)},
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
    is_dummy_ = true;
    return;
  }

  // Build Polytope contractor from system.
  linear_relax_combo_ = make_unique<ibex::LinearizerCombo>(
      *system_, ibex::LinearizerCombo::XNEWTON);
  ctc_ = make_unique<ibex::CtcPolytopeHull>(*linear_relax_combo_);

  // Build input.
  DynamicBitset& input{mutable_input()};
  for (const Formula& f : formulas_) {
    for (const Variable& var : f.GetFreeVariables()) {
      input.set(box.index(var));
    }
  }
}

void ContractorIbexPolytope::Prune(ContractorStatus* cs) const {
  DREAL_ASSERT(!is_dummy_ && ctc_);
  Box::IntervalVector& iv{cs->mutable_box().mutable_interval_vector()};
  const Box::IntervalVector old_iv = iv;
  DREAL_LOG_TRACE("ContractorIbexPolytope::Prune");
  ctc_->contract(iv);
  bool changed{false};
  // Update output.
  if (iv.is_empty()) {
    changed = true;
    cs->mutable_output().set();
  } else {
    for (int i = 0; i < old_iv.size(); ++i) {
      if (old_iv[i] != iv[i]) {
        cs->mutable_output().set(i);
        changed = true;
      }
    }
  }
  // Update used constraints.
  if (changed) {
    cs->AddUsedConstraint(formulas_);
    if (DREAL_LOG_TRACE_ENABLED) {
      ostringstream oss;
      DisplayDiff(oss, cs->box().variables(), old_iv, iv);
      DREAL_LOG_TRACE("Changed\n{}", oss.str());
    }
  } else {
    DREAL_LOG_TRACE("NO CHANGE");
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

bool ContractorIbexPolytope::is_dummy() const { return is_dummy_; }

}  // namespace dreal
