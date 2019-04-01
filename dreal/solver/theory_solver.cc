#include "dreal/solver/theory_solver.h"

#include <iostream>
#include <limits>
#include <memory>
#include <utility>

#include "dreal/contractor/contractor_forall.h"
#include "dreal/solver/context.h"
#include "dreal/solver/filter_assertion.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/solver/icp.h"
#include "dreal/util/assert.h"
#include "dreal/util/logging.h"
#include "dreal/util/stat.h"

namespace dreal {

using std::cout;
using std::numeric_limits;
using std::set;
using std::vector;

TheorySolver::TheorySolver(const Config& config)
    : config_{config}, icp_{config_} {}

namespace {
bool DefaultTerminationCondition(const Box::IntervalVector& old_iv,
                                 const Box::IntervalVector& new_iv) {
  DREAL_ASSERT(!new_iv.is_empty());
  constexpr double threshold{0.01};
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
    DREAL_ASSERT(!std::isnan(improvement));
    if (improvement >= threshold) {
      return false;
    }
  }
  // If an execution reaches at this point, it means there was no
  // significant improvement. So return true to stop fixed-point
  // computation
  return true;
}

class TheorySolverStat : public Stat {
 public:
  explicit TheorySolverStat(const bool enabled) : Stat{enabled} {}
  TheorySolverStat(const TheorySolverStat&) = default;
  TheorySolverStat(TheorySolverStat&&) = default;
  TheorySolverStat& operator=(const TheorySolverStat&) = default;
  TheorySolverStat& operator=(TheorySolverStat&&) = default;
  ~TheorySolverStat() override {
    if (enabled()) {
      using fmt::print;
      print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of CheckSat",
            "Theory level", num_check_sat_);
    }
  }

  int num_check_sat_{0};
};

}  // namespace

optional<Contractor> TheorySolver::BuildContractor(
    const vector<Formula>& assertions,
    ContractorStatus* const contractor_status) {
  Box& box = contractor_status->mutable_box();
  if (assertions.empty()) {
    return make_contractor_integer(box, config_);
  }
  vector<Contractor> ctcs;
  for (const Formula& f : assertions) {
    switch (FilterAssertion(f, &box)) {
      case FilterAssertionResult::NotFiltered:
        /* No OP */
        break;
      case FilterAssertionResult::FilteredWithChange:
        contractor_status->AddUsedConstraint(f);
        if (box.empty()) {
          return {};
        }
        continue;
      case FilterAssertionResult::FilteredWithoutChange:
        continue;
    }
    auto it = contractor_cache_.find(f);
    if (it == contractor_cache_.end()) {
      // There is no contractor for `f`, build one.
      DREAL_LOG_DEBUG("TheorySolver::BuildContractor: {}", f);
      if (is_forall(f)) {
        // We should have `inner_delta < epsilon < delta`.
        const double delta{config_.precision()};
        const double epsilon{delta * 0.99};
        const double inner_delta{epsilon * 0.99};
        DREAL_ASSERT(inner_delta < epsilon && epsilon < delta);
        const Contractor ctc{make_contractor_forall<Context>(
            f, box, epsilon, inner_delta, config_)};
        ctcs.emplace_back(make_contractor_fixpoint(DefaultTerminationCondition,
                                                   {ctc}, config_));
      } else {
        ctcs.emplace_back(make_contractor_ibex_fwdbwd(f, box, config_));
      }
      // Add it to the cache.
      contractor_cache_.emplace_hint(it, f, ctcs.back());
    } else {
      // Cache hit!
      ctcs.emplace_back(it->second);
    }
  }
  // Add integer contractor.
  ctcs.push_back(make_contractor_integer(box, config_));

  if (config_.use_polytope()) {
    // Add polytope contractor.
    ctcs.push_back(make_contractor_ibex_polytope(assertions, box, config_));
  }
  if (config_.use_worklist_fixpoint()) {
    return make_contractor_worklist_fixpoint(DefaultTerminationCondition, ctcs,
                                             config_);
  } else {
    return make_contractor_fixpoint(DefaultTerminationCondition, ctcs, config_);
  }
}

vector<FormulaEvaluator> TheorySolver::BuildFormulaEvaluator(
    const vector<Formula>& assertions) {
  vector<FormulaEvaluator> formula_evaluators;
  formula_evaluators.reserve(assertions.size());
  // We should have `inner_delta < epsilon < delta`.
  const double delta{config_.precision()};
  const double epsilon{0.99 * delta};
  const double inner_delta{0.99 * epsilon};
  DREAL_ASSERT(inner_delta < epsilon && epsilon < delta);
  for (const Formula& f : assertions) {
    auto it = formula_evaluator_cache_.find(f);
    if (it == formula_evaluator_cache_.end()) {
      DREAL_LOG_DEBUG("TheorySolver::BuildFormulaEvaluator: {}", f);
      if (is_forall(f)) {
        formula_evaluators.push_back(
            make_forall_formula_evaluator(f, epsilon, inner_delta));
      } else {
        formula_evaluators.push_back(make_relational_formula_evaluator(f));
      }
      formula_evaluator_cache_.emplace_hint(it, f, formula_evaluators.back());
    } else {
      formula_evaluators.push_back(it->second);
    }
  }
  return formula_evaluators;
}

bool TheorySolver::CheckSat(const Box& box, const vector<Formula>& assertions) {
  static TheorySolverStat stat{DREAL_LOG_INFO_ENABLED};
  stat.num_check_sat_++;
  DREAL_LOG_DEBUG("TheorySolver::CheckSat()");
  ContractorStatus contractor_status(box);

  // Icp Step
  const optional<Contractor> contractor{
      BuildContractor(assertions, &contractor_status)};
  if (contractor) {
    icp_.CheckSat(*contractor, BuildFormulaEvaluator(assertions),
                  &contractor_status);
    if (contractor_status.box().empty()) {
      explanation_ = contractor_status.Explanation();
      return false;
    } else {
      model_ = contractor_status.box();
      return true;
    }
    return !contractor_status.box().empty();
  } else {
    DREAL_ASSERT(contractor_status.box().empty());
    explanation_ = contractor_status.Explanation();
    return false;
  }
}

const Box& TheorySolver::GetModel() const {
  DREAL_LOG_DEBUG("TheorySolver::GetModel():\n{}", model_);
  return model_;
}

const set<Formula>& TheorySolver::GetExplanation() const {
  return explanation_;
}

}  // namespace dreal
