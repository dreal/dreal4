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
#include "dreal/solver/theory_solver.h"

#include <atomic>
#include <iostream>
#include <limits>
#include <memory>
#include <utility>

#include <nlohmann/json.hpp>

#include "dreal/contractor/contractor_forall.h"
#include "dreal/solver/context.h"
#include "dreal/solver/filter_assertion.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/solver/icp_parallel.h"
#include "dreal/solver/icp_seq.h"
#include "dreal/util/assert.h"
#include "dreal/util/logging.h"
#include "dreal/util/stat.h"
#include "dreal/util/timer.h"

namespace dreal {

using std::cout;
using std::make_unique;
using std::numeric_limits;
using std::set;
using std::vector;

TheorySolver::TheorySolver(const Config& config)
    : config_{config}, icp_{nullptr} {
  if (config_.number_of_jobs() > 1) {
    icp_ = make_unique<IcpParallel>(config_);
  } else {
    icp_ = make_unique<IcpSeq>(config_);
  }
}

namespace {
bool DefaultTerminationCondition(const Box::IntervalVector& old_iv,
                                 const Box::IntervalVector& new_iv) {
  DREAL_ASSERT(!new_iv.is_empty());
  constexpr double kThreshold{0.01};
  // If there is a dimension which is improved more than
  // threshold, we continue the current fixed-point computation
  // (return false).
  for (int i{0}; i < old_iv.size(); ++i) {
    const double new_i{new_iv[i].diam()};
    // If the width of new interval is +oo, it has no improvement
    if (new_i == numeric_limits<double>::infinity()) {
      continue;
    }
    // If the i-th dimension was already a point, nothing to improve.
    if (old_iv[i].is_degenerated()) {
      continue;
    }
    const double old_i{old_iv[i].diam()};
    const double improvement{1 - new_i / old_i};
    DREAL_ASSERT(!std::isnan(improvement));
    if (improvement >= kThreshold) {
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
  TheorySolverStat(const TheorySolverStat&) = delete;
  TheorySolverStat(TheorySolverStat&&) = delete;
  TheorySolverStat& operator=(const TheorySolverStat&) = delete;
  TheorySolverStat& operator=(TheorySolverStat&&) = delete;
  ~TheorySolverStat() override {
    if (enabled()) {
      using fmt::print;
      print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of CheckSat",
            "Theory level", num_check_sat_);
      print(cout, "{:<45} @ {:<20} = {:>15f} sec\n",
            "Total time spent in CheckSat", "Theory level",
            timer_check_sat_.seconds());
    }
  }

  void increase_num_check_sat() { increase(&num_check_sat_); }

  Timer timer_check_sat_;

 private:
  std::atomic<int> num_check_sat_{0};
};

/// Helper class to implement "--dump-theory-literals" option. It
/// collects a list of theory literals for each round and print outs
/// the information (list of list of literals) when an instance of
/// this class is destructed.
class DumpTheoryLiteralsHelper {
 public:
  /// Constructor.
  ///
  /// Its destructor only outputs the information when `enabled_` is true.
  explicit DumpTheoryLiteralsHelper(bool enabled) : enabled_{enabled} {}
  ~DumpTheoryLiteralsHelper() {
    if (enabled_) {
      std::cout << data_ << "\n";
    }
  }

  /// Starts a new round of theory-solving.
  void StartNewRound() { data_.push_back(nlohmann::json{}); }

  /// Adds a literfal `f` to the data.
  void AddLiteral(const Formula& f) { data_.back().push_back(f.to_string()); }

 private:
  bool enabled_{false};
  nlohmann::json data_;
};

}  // namespace

optional<Contractor> TheorySolver::BuildContractor(
    const vector<Formula>& assertions,
    ContractorStatus* const contractor_status) {
  Box& box = contractor_status->mutable_box();
  if (assertions.empty()) {
    return make_contractor_integer(box, config_);
  }
  DREAL_LOG_TRACE("TheorySolver::BuildContractor: Filtering Assertions\n{}",
                  box);
  vector<Contractor> ctcs;
  Box old_box;
  for (const Formula& f : assertions) {
    old_box = box;
    switch (FilterAssertion(f, &box)) {
      case FilterAssertionResult::NotFiltered:
        DREAL_LOG_TRACE("TheorySolver::BuildContractor: {} - Not Filtered.", f);
        if (old_box != box) {
          contractor_status->AddUsedConstraint(f);
        }
        break;
      case FilterAssertionResult::FilteredWithChange:
        DREAL_LOG_TRACE(
            "TheorySolver::BuildContractor: {} - Filtered with Change.\n{}", f,
            box);
        contractor_status->AddUsedConstraint(f);
        if (box.empty()) {
          for (const auto& v : f.GetFreeVariables()) {
            contractor_status->AddUnsatWitness(v);
          }
          DREAL_LOG_TRACE(
              "TheorySolver::BuildContractor: {} - Filtered with Change => "
              "EMPTY BOX",
              f);
          return {};
        }
        continue;
      case FilterAssertionResult::FilteredWithoutChange:
        continue;
    }
    auto it = contractor_cache_.find(f);
    if (it == contractor_cache_.end()) {
      // There is no contractor for `f`, build one.
      DREAL_LOG_DEBUG(
          "TheorySolver::BuildContractor: Turn {} into a contractor", f);
      if (is_forall(f)) {
        // We should have `inner_delta < epsilon < delta`.
        const double delta{config_.precision()};
        const double epsilon{delta * 0.5};
        const double inner_delta{epsilon * 0.5};
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
  if (DREAL_LOG_TRACE_ENABLED) {
    for (const auto& ctc : ctcs) {
      DREAL_LOG_TRACE("TheorySolver::BuildContractor: CTC = {}", ctc);
    }
    if (ctcs.empty()) {
      DREAL_LOG_TRACE("TheorySolver::BuildContractor: CTCS = empty");
    }
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
        formula_evaluators.push_back(make_forall_formula_evaluator(
            f, epsilon, inner_delta, config_.number_of_jobs()));
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
  static DumpTheoryLiteralsHelper dump_theory_literals{
      config_.dump_theory_literals()};
  stat.increase_num_check_sat();
  TimerGuard check_sat_timer_guard(&stat.timer_check_sat_, stat.enabled(),
                                   true /* start_timer */);

  if (config_.dump_theory_literals()) {
    dump_theory_literals.StartNewRound();
    for (const auto& f : assertions) {
      dump_theory_literals.AddLiteral(f);
    }
  }

  DREAL_LOG_DEBUG("TheorySolver::CheckSat()");
  ContractorStatus contractor_status(box);

  // Icp Step
  const optional<Contractor> contractor{
      BuildContractor(assertions, &contractor_status)};
  if (contractor) {
    icp_->CheckSat(*contractor, BuildFormulaEvaluator(assertions),
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
