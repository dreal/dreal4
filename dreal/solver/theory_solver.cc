#include "dreal/solver/theory_solver.h"

#include <limits>
#include <memory>
#include <utility>

#include "dreal/contractor/contractor_forall.h"
#include "dreal/solver/context.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/solver/icp.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::move;
using std::numeric_limits;
using std::unordered_set;
using std::vector;

TheorySolver::TheorySolver(const Config& config, const Box& box)
    : config_{config}, box_{box}, contractor_status_{box} {}

TheorySolver::~TheorySolver() {
  DREAL_LOG_DEBUG(
      "TheorySolver::~TheorySolver() - # of TheorySolver::CheckSat() = {}",
      num_check_sat);
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
    auto it = contractor_cache_.find(f);
    if (it == contractor_cache_.end()) {
      // There is no contractor for `f`, build one.
      DREAL_LOG_DEBUG("TheorySolver::BuildContractor: {}", f);
      if (is_forall(f)) {
        // We should have `inner_delta < epsilon < delta`.
        const double epsilon = config_.precision() * 0.99;
        const double inner_delta = epsilon * 0.99;
        const Contractor ctc{make_contractor_forall<Context>(
            f, box_, epsilon, inner_delta, config_.use_polytope_in_forall())};
        ctcs.emplace_back(
            make_contractor_fixpoint(termination_condition, {ctc}));
      } else {
        ctcs.emplace_back(make_contractor_ibex_fwdbwd(f, box_));
      }
      // Add it to the cache.
      contractor_cache_.emplace_hint(it, f, ctcs.back());
    } else {
      // Cache hit!
      ctcs.emplace_back(it->second);
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

vector<FormulaEvaluator> TheorySolver::BuildFormulaEvaluator(
    const vector<Formula>& assertions) {
  vector<FormulaEvaluator> formula_evaluators;
  const double delta = config_.precision();
  const double epsilon = 0.99 * delta;
  const double inner_delta = 0.99 * epsilon;
  for (const Formula& f : assertions) {
    auto it = formula_evaluator_cache_.find(f);
    if (it == formula_evaluator_cache_.end()) {
      DREAL_LOG_DEBUG("TheorySolver::BuildFormulaEvaluator: {}", f);
      if (is_forall(f)) {
        formula_evaluators.push_back(make_forall_formula_evaluator(
            f, box_.variables(), epsilon, inner_delta));
      } else {
        formula_evaluators.push_back(
            make_relational_formula_evaluator(f, box_.variables()));
      }
      formula_evaluator_cache_.emplace_hint(it, f, formula_evaluators.back());
    } else {
      formula_evaluators.push_back(it->second);
    }
  }
  return formula_evaluators;
}

bool TheorySolver::CheckSat(const vector<Formula>& assertions) {
  num_check_sat++;
  DREAL_LOG_DEBUG("TheorySolver::CheckSat()");
  assert(box_.size() > 0);
  contractor_status_ = ContractorStatus(box_);

  // Icp Step
  Icp icp(BuildContractor(assertions), BuildFormulaEvaluator(assertions),
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
