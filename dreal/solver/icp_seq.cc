#include "dreal/solver/icp_seq.h"

#include <tuple>
#include <utility>

#include "dreal/solver/branch.h"
#include "dreal/solver/icp_stat.h"
#include "dreal/util/interrupt.h"
#include "dreal/util/logging.h"

using std::pair;
using std::tie;
using std::vector;

namespace dreal {

IcpSeq::IcpSeq(const Config& config) : Icp{config} {}

bool IcpSeq::CheckSat(const Contractor& contractor,
                      const vector<FormulaEvaluator>& formula_evaluators,
                      ContractorStatus* const cs) {
  // Use the stacking policy set by the configuration.
  stack_left_box_first_ = config().stack_left_box_first();
  static IcpStat stat{DREAL_LOG_INFO_ENABLED};
  DREAL_LOG_DEBUG("IcpSeq::CheckSat()");
  // Stack of Box x BranchingPoint.
  vector<pair<Box, int>> stack;
  stack.emplace_back(
      cs->box(),
      // -1 indicates that the very first box does not come from a branching.
      -1);

  // `current_box` always points to the box in the contractor status
  // as a mutable reference.
  Box& current_box{cs->mutable_box()};
  // `current_branching_point` always points to the branching_point in
  // the contractor status as a mutable reference.
  int& current_branching_point{cs->mutable_branching_point()};

  TimerGuard prune_timer_guard(&stat.timer_prune_, stat.enabled(),
                               false /* start_timer */);
  TimerGuard eval_timer_guard(&stat.timer_eval_, stat.enabled(),
                              false /* start_timer */);
  TimerGuard branch_timer_guard(&stat.timer_branch_, stat.enabled(),
                                false /* start_timer */);

  while (!stack.empty()) {
    DREAL_LOG_DEBUG("IcpSeq::CheckSat() Loop Head");

    // Note that 'DREAL_CHECK_INTERRUPT' is only defined in setup.py,
    // when we build dReal python package.
#ifdef DREAL_CHECK_INTERRUPT
    if (g_interrupted) {
      DREAL_LOG_DEBUG("KeyboardInterrupt(SIGINT) Detected.");
      throw std::runtime_error("KeyboardInterrupt(SIGINT) Detected.");
    }
#endif

    // 1. Pop the current box from the stack
    tie(current_box, current_branching_point) = stack.back();
    stack.pop_back();

    // 2. Prune the current box.
    DREAL_LOG_TRACE("IcpSeq::CheckSat() Current Box:\n{}", current_box);
    prune_timer_guard.resume();
    contractor.Prune(cs);
    prune_timer_guard.pause();
    stat.num_prune_++;
    DREAL_LOG_TRACE("IcpSeq::CheckSat() After pruning, the current box =\n{}",
                    current_box);

    if (current_box.empty()) {
      // 3.1. The box is empty after pruning.
      DREAL_LOG_DEBUG("IcpSeq::CheckSat() Box is empty after pruning");
      continue;
    }
    // 3.2. The box is non-empty. Check if the box is still feasible
    // under evaluation and it's small enough.
    eval_timer_guard.resume();
    const optional<ibex::BitSet> evaluation_result{
        EvaluateBox(formula_evaluators, current_box, config().precision(), cs)};
    if (!evaluation_result) {
      // 3.2.1. We detect that the current box is not a feasible solution.
      DREAL_LOG_DEBUG(
          "IcpSeq::CheckSat() Detect that the current box is not feasible by "
          "evaluation:\n{}",
          current_box);
      eval_timer_guard.pause();
      continue;
    }
    if (evaluation_result->empty()) {
      // 3.2.2. delta-SAT : We find a box which is smaller enough.
      DREAL_LOG_DEBUG("IcpSeq::CheckSat() Found a delta-box:\n{}", current_box);
      return true;
    }
    eval_timer_guard.pause();

    // 3.2.3. This box is bigger than delta. Need branching.
    branch_timer_guard.resume();
    if (!Branch(current_box, *evaluation_result, stack_left_box_first_,
                &stack)) {
      DREAL_LOG_DEBUG(
          "IcpSeq::CheckSat() Found that the current box is not satisfying "
          "delta-condition but it's not bisectable.:\n{}",
          current_box);
      return true;
    }
    branch_timer_guard.pause();

    // We alternate between adding-the-left-box-first policy and
    // adding-the-right-box-first policy.
    stack_left_box_first_ = !stack_left_box_first_;
    stat.num_branch_++;
  }
  DREAL_LOG_DEBUG("IcpSeq::CheckSat() No solution");
  return false;
}
}  // namespace dreal
