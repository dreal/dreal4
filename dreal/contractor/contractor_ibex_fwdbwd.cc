#include "dreal/contractor/contractor_ibex_fwdbwd.h"

#include <sstream>
#include <utility>

#include "dreal/util/logging.h"
#include "dreal/util/math.h"
#include "dreal/util/stat.h"

using std::cout;
using std::make_unique;
using std::move;
using std::ostream;
using std::ostringstream;

namespace dreal {

namespace {
class ContractorIbexFwdbwdStat : public Stat {
 public:
  explicit ContractorIbexFwdbwdStat(const bool enabled) : Stat{enabled} {};
  ContractorIbexFwdbwdStat(const ContractorIbexFwdbwdStat&) = default;
  ContractorIbexFwdbwdStat(ContractorIbexFwdbwdStat&&) = default;
  ContractorIbexFwdbwdStat& operator=(const ContractorIbexFwdbwdStat&) =
      default;
  ContractorIbexFwdbwdStat& operator=(ContractorIbexFwdbwdStat&&) = default;
  ~ContractorIbexFwdbwdStat() override {
    if (enabled()) {
      using fmt::print;
      print(cout, "{:<45} @ {:<20} = {:>15}\n",
            "Total # of ibex-fwdbwd Pruning", "Pruning level", num_pruning_);
      print(cout, "{:<45} @ {:<20} = {:>15}\n",
            "Total # of ibex-fwdbwd Pruning (zero-effect)", "Pruning level",
            num_zero_effect_pruning_);
    }
  }

  int num_zero_effect_pruning_{0};
  int num_pruning_{0};
};
}  // namespace

//---------------------------------------
// Implementation of ContractorIbexFwdbwd
//---------------------------------------
ContractorIbexFwdbwd::ContractorIbexFwdbwd(Formula f, const Box& box,
                                           const Config& config)
    : ContractorCell{Contractor::Kind::IBEX_FWDBWD,
                     ibex::BitSet::empty(box.size()), config},
      f_{move(f)},
      ibex_converter_{box},
      old_iv_{1 /* Will be overwritten anyway */} {
  // Build num_ctr and ctc_.
  expr_ctr_.reset(ibex_converter_.Convert(f_));
  if (expr_ctr_) {
    num_ctr_ = make_unique<ibex::NumConstraint>(ibex_converter_.variables(),
                                                *expr_ctr_);
    ctc_ = make_unique<ibex::CtcFwdBwd>(*num_ctr_);
    // Build input.
    ibex::BitSet& input{mutable_input()};
    for (const Variable& var : f_.GetFreeVariables()) {
      input.add(box.index(var));
    }
  }
}

void ContractorIbexFwdbwd::Prune(ContractorStatus* cs) const {
  static ContractorIbexFwdbwdStat stat{DREAL_LOG_INFO_ENABLED};
  if (ctc_) {
    Box::IntervalVector& iv{cs->mutable_box().mutable_interval_vector()};
    old_iv_ = iv;
    DREAL_LOG_TRACE("ContractorIbexFwdbwd::Prune");
    DREAL_LOG_TRACE("CTC = {}", *num_ctr_);
    DREAL_LOG_TRACE("F = {}", f_);
    ctc_->contract(iv);
    stat.num_pruning_++;
    bool changed{false};
    // Update output.
    if (iv.is_empty()) {
      changed = true;
      cs->mutable_output().fill(0, cs->box().size() - 1);
    } else {
      for (int i = 0, idx = ctc_->output->min(); i < ctc_->output->size();
           ++i, idx = ctc_->output->next(idx)) {
        if (old_iv_[idx] != iv[idx]) {
          cs->mutable_output().add(idx);
          changed = true;
        }
      }
    }
    // Update used constraints.
    if (changed) {
      cs->AddUsedConstraint(f_);
      if (DREAL_LOG_TRACE_ENABLED) {
        ostringstream oss;
        DisplayDiff(oss, cs->box().variables(), old_iv_,
                    cs->box().interval_vector());
        DREAL_LOG_TRACE("Changed\n{}", oss.str());
      }
    } else {
      stat.num_zero_effect_pruning_++;
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
