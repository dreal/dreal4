#include "dreal/contractor/contractor_ibex_fwdbwd.h"

#include <algorithm>
#include <cmath>
#include <limits>
#include <memory>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dreal/util/logging.h"
#include "dreal/util/math.h"

using std::accumulate;
using std::make_unique;
using std::move;
using std::numeric_limits;
using std::ostream;
using std::ostringstream;
using std::runtime_error;
using std::shared_ptr;
using std::unique_ptr;
using std::unordered_map;
using std::vector;

namespace dreal {

//---------------------------------------
// Implementation of ContractorIbexFwdbwd
//---------------------------------------
ContractorIbexFwdbwd::ContractorIbexFwdbwd(Formula f, const Box& box)
    : ContractorCell{Contractor::Kind::IBEX_FWDBWD,
                     ibex::BitSet::empty(box.size())},
      f_{move(f)},
      ibex_converter_{box} {
  // Build num_ctr and ctc_.
  expr_ctr_.reset(ibex_converter_.Convert(f_));
  if (expr_ctr_) {
    num_ctr_.reset(
        new ibex::NumConstraint(ibex_converter_.variables(), *expr_ctr_));
  }
  if (num_ctr_) {
    ctc_.reset(new ibex::CtcFwdBwd{*num_ctr_});
  }
  // Build input.
  ibex::BitSet& input{get_mutable_input()};
  for (const Variable& var : f_.GetFreeVariables()) {
    input.add(box.index(var));
  }
}

ContractorIbexFwdbwd::~ContractorIbexFwdbwd() {}

void ContractorIbexFwdbwd::Prune(ContractorStatus* cs) const {
  if (ctc_) {
    Box::IntervalVector& iv{
        cs->get_mutable_box().get_mutable_interval_vector()};
    static Box::IntervalVector old_iv{iv};
    old_iv = iv;
    DREAL_LOG_TRACE("ContractorIbexFwdbwd::Prune");
    DREAL_LOG_TRACE("CTC = {}", *num_ctr_);
    DREAL_LOG_TRACE("F = {}", f_);
    ctc_->contract(iv);
    bool changed{false};
    // Update output.
    if (iv.is_empty()) {
      changed = true;
      cs->get_mutable_output().fill(0, cs->box().size() - 1);
    } else {
      for (int i = 0; i < old_iv.size(); ++i) {
        if (old_iv[i] != iv[i]) {
          cs->get_mutable_output().add(i);
          changed = true;
        }
      }
    }
    // Update used constraints.
    if (changed) {
      cs->AddUsedConstraint(f_);
      ostringstream oss;
      DisplayDiff(oss, cs->box().variables(), old_iv,
                  cs->box().interval_vector());
      DREAL_LOG_TRACE("Changed\n{}", oss.str());
    } else {
      DREAL_LOG_TRACE("NO CHANGE");
    }
  }
}

Box::Interval ContractorIbexFwdbwd::Evaluate(const Box& box) const {
  return num_ctr_->f.eval(box.interval_vector());
}

ostream& ContractorIbexFwdbwd::display(ostream& os) const {
  if (num_ctr_) {
    return os << "IbexFwdbwd(" << *num_ctr_ << ")";
  } else {
    return os << "IbexFwdbwd()";
  }
}

}  // namespace dreal
