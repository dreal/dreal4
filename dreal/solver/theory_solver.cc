#include "dreal/solver/theory_solver.h"

#include <limits>
#include <memory>
#include <stdexcept>
#include <utility>

#include "dreal/contractor/contractor_forall.h"
#include "dreal/solver/context.h"
#include "dreal/solver/evaluator.h"
#include "dreal/solver/icp.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::move;
using std::numeric_limits;
using std::runtime_error;
using std::unordered_set;
using std::unordered_set;
using std::vector;

TheorySolver::TheorySolver(const Config& config, const Box& box)
    : config_{config}, box_{box}, contractor_status_{box} {}

TheorySolver::~TheorySolver() {
  DREAL_LOG_DEBUG("# of TheorySolver::CheckSat() = {}", num_check_sat);
}

Contractor TheorySolver::BuildContractor(const vector<Formula>& assertions) {
  if (assertions.empty()) {
    return make_contractor_integer(box_);
  }

  static TerminationCondition termination_condition{
      [](const Box::IntervalVector& old_iv, const Box::IntervalVector& new_iv) {
        if (new_iv.is_empty()) {
          return true;
        }
        const double threshold{0.01};
        // If there is a dimension which is improved more than
        // threshold, we continue the current fixed-point computation
        // (return false).
        for (int i{0}; i < old_iv.size(); ++i) {
          const double new_i{new_iv[i].diam()};
          const double old_i{old_iv[i].diam()};
          // If the width of new interval is +oo, it has no improvement
          if (new_i == numeric_limits<double>::infinity()) {
            continue;
          }
          // If the i-th dimension was already a point, nothing to improve.
          if (old_i == 0) {
            continue;
          }
          const double improvement{1 - new_i / old_i};
          assert(!std::isnan(improvement));
          if (improvement >= threshold) {
            return false;
          }
        }
        // If an execution reaches at this point, it means there was no
        // significant improvement. So return true to stop fixed-point
        // computation
        return true;
      }};

  vector<Contractor> ctcs;
  for (const Formula& f : assertions) {
    if (!is_forall(f)) {
      auto it = ibex_contractor_cache_.find(f);
      if (it == ibex_contractor_cache_.end()) {
        DREAL_LOG_DEBUG("TheorySolver::BuildContractor: {}", f);
        const Contractor ctc{make_contractor_ibex_fwdbwd(f, box_)};
        ibex_contractor_cache_.emplace_hint(it, f, ctc);
        ctcs.emplace_back(move(ctc));
      } else {
        ctcs.emplace_back(it->second);
      }
    } else {
      const Contractor ctc{make_contractor_forall<Context>(
          get_quantified_variables(f), get_quantified_formula(f), box_,
          config_.precision(), config_.precision() / 2,
          config_.use_polytope_in_forall())};
      ctcs.emplace_back(make_contractor_fixpoint(termination_condition, {ctc}));
    }
  }
  // Add integer contractor.
  ctcs.push_back(make_contractor_integer(box_));

  if (config_.use_polytope()) {
    // Add polytope contractor.
    ctcs.push_back(make_contractor_ibex_polytope(assertions, box_));
  }

  return make_contractor_fixpoint(termination_condition, move(ctcs));
}

vector<Evaluator> TheorySolver::BuildEvaluator(
    const vector<Formula>& assertions) {
  vector<Evaluator> evaluators;
  for (const Formula& f : assertions) {
    auto it = evaluator_cache_.find(f);
    if (it == evaluator_cache_.end()) {
      DREAL_LOG_DEBUG("TheorySolver::BuildEvaluator: {}", f);
      evaluators.emplace_back(f, box_.variables(), config_.precision());
      evaluator_cache_.emplace_hint(it, f, evaluators.back());
    } else {
      evaluators.push_back(it->second);
    }
  }
  return evaluators;
}

bool TheorySolver::CheckSat(const vector<Formula>& assertions) {
  num_check_sat++;
  DREAL_LOG_DEBUG("TheorySolver::CheckSat()");
  contractor_status_ = ContractorStatus(box_);

  // Icp Step
  Icp icp(BuildContractor(assertions), BuildEvaluator(assertions),
          config_.precision());
  icp.CheckSat(&contractor_status_);
  if (contractor_status_.box().empty()) {
    status_ = Status::UNSAT;
    return false;
  } else {
    status_ = Status::SAT;
    return true;
  }
}

Box TheorySolver::GetModel() const {
  assert(status_ == Status::SAT);
  DREAL_LOG_DEBUG("TheorySolver::GetModel():\n{}", contractor_status_.box());
  return contractor_status_.box();
}

const unordered_set<Formula, hash_value<Formula>> TheorySolver::GetExplanation()
    const {
  assert(status_ == Status::UNSAT);
  return contractor_status_.explanation();
}

}  // namespace dreal
