#include "dreal/solver/icp_parallel.h"

#include <atomic>
#include <tuple>
#include <utility>

#include "dreal/solver/branch.h"
#include "dreal/solver/icp_stat.h"
#include "dreal/util/assert.h"
#include "dreal/util/cds.h"
#include "dreal/util/interrupt.h"
#include "dreal/util/logging.h"

using std::atomic;
using std::pair;
using std::vector;

namespace dreal {

namespace {

bool ParallelBranch(const ibex::BitSet& bitset, const bool stack_left_box_first,
                    Box* const box, Stack<Box>* const global_stack,
                    atomic<int>* const number_of_boxes) {
  const pair<double, int> max_diam_and_idx{FindMaxDiam(*box, bitset)};
  const int branching_point{max_diam_and_idx.second};
  if (branching_point >= 0) {
    const auto boxes = box->bisect(branching_point);
    const Box* box1_ptr{nullptr};
    const Box* box2_ptr{nullptr};
    if (stack_left_box_first) {
      box1_ptr = &boxes.first;
      box2_ptr = &boxes.second;
    } else {
      box2_ptr = &boxes.first;
      box1_ptr = &boxes.second;
    }
    const Box& box1{*box1_ptr};
    const Box& box2{*box2_ptr};
    number_of_boxes->fetch_add(1, std::memory_order_relaxed);
    global_stack->push(box1);
    *box = box2;
    return true;
  }
  // Fail to find a branching point.
  return false;
}

void Worker(const Contractor& contractor, const Config& config,
            const vector<FormulaEvaluator>& formula_evaluators, const int id,
            const bool main_thread, Stack<Box>* const global_stack,
            ContractorStatus* const cs, atomic<int>* const found_delta_sat,
            atomic<int>* const number_of_boxes) {
  thread_local IcpStat stat{DREAL_LOG_INFO_ENABLED, id};
  TimerGuard prune_timer_guard(&stat.timer_prune_, stat.enabled(),
                               false /* start_timer */);
  TimerGuard eval_timer_guard(&stat.timer_eval_, stat.enabled(),
                              false /* start_timer */);
  TimerGuard branch_timer_guard(&stat.timer_branch_, stat.enabled(),
                                false /* start_timer */);

  thread_local CdsScopeGuard cds_scope_guard(!main_thread);

  bool stack_left_box_first{config.stack_left_box_first()};

  // `current_box` always points to the box in the contractor status
  // as a mutable reference.
  Box& current_box{cs->mutable_box()};

  // When this flag is true, we need to pop a box from the stack. Otherwise, it
  // indicates that we can work with the box inside of the ContractorStatus.
  bool need_to_pop{true};

  while ((*found_delta_sat == -1) &&
         (number_of_boxes->load(std::memory_order_acquire) > 0)) {
    // Note that 'DREAL_CHECK_INTERRUPT' is only defined in setup.py,
    // when we build dReal python package.
#ifdef DREAL_CHECK_INTERRUPT
    if (g_interrupted) {
      DREAL_LOG_DEBUG("KeyboardInterrupt(SIGINT) Detected.");
      throw std::runtime_error("KeyboardInterrupt(SIGINT) Detected.");
    }
#endif

    // 1. Pick a box from the global stack if needed.
    if (need_to_pop) {
      if (!global_stack->pop(current_box)) {
        continue;
      }
    }
    need_to_pop = true;

    // 2. Prune the current box.
    prune_timer_guard.resume();
    contractor.Prune(cs);
    prune_timer_guard.pause();
    if (stat.enabled()) {
      stat.num_prune_++;
    }

    if (current_box.empty()) {
      // 3.1. The box is empty after pruning.
      number_of_boxes->fetch_sub(1, std::memory_order_acq_rel);
      continue;
    }

    // 3.2. The box is non-empty. Check if the box is still feasible
    // under evaluation and it's small enough.
    eval_timer_guard.resume();
    const optional<ibex::BitSet> evaluation_result{
        EvaluateBox(formula_evaluators, current_box, config.precision(), cs)};
    if (!evaluation_result) {
      // 3.2.1. We detect that the current box is not a feasible solution.
      number_of_boxes->fetch_sub(1, std::memory_order_acq_rel);
      DREAL_LOG_DEBUG(
          "IcpParallel::Worker() Detect that the current box is not feasible "
          "by evaluation:\n{}",
          current_box);
      continue;
    }
    if (evaluation_result->empty()) {
      // 3.2.2. delta - SAT: We find a box which is smaller enough.
      DREAL_LOG_DEBUG("IcpParallel::Worker() Found a delta-box:\n{}",
                      current_box);
      *found_delta_sat = id;
      return;
    }
    eval_timer_guard.pause();

    // 3.2.3. This box is bigger than delta. Need branching.
    branch_timer_guard.resume();
    if (!ParallelBranch(*evaluation_result, stack_left_box_first, &current_box,
                        global_stack, number_of_boxes)) {
      DREAL_LOG_DEBUG(
          "IcpParallel::Worker() Found that the current box is not "
          "satisfying "
          "delta-condition but it's not bisectable.:\n{}",
          current_box);
      *found_delta_sat = id;
      return;
    }
    branch_timer_guard.pause();

    need_to_pop = false;

    // We alternate between adding-the-left-box-first policy and
    // adding-the-right-box-first policy.
    stack_left_box_first = !stack_left_box_first;
    stat.num_branch_++;
  }
}
}  // namespace

IcpParallel::IcpParallel(const Config& config)
    : Icp{config}, pool_{static_cast<size_t>(config.number_of_jobs() - 1)} {
  results_.reserve(config.number_of_jobs() - 1);
  status_vector_.reserve(config.number_of_jobs());
}

bool IcpParallel::CheckSat(const Contractor& contractor,
                           const vector<FormulaEvaluator>& formula_evaluators,
                           ContractorStatus* const cs) {
  // Initial Prune
  contractor.Prune(cs);
  if (cs->box().empty()) {
    return false;
  }

  results_.clear();
  status_vector_.clear();

  // -1 indicates that the process does not find a solution yet. i >= 0
  // indicates that the i-th worker already found a solution.
  atomic<int> found_delta_sat{-1};
  static CdsInit cds_init{
      true /* main thread is using lock-free containers. */};
  Stack<Box> global_stack;

  const int number_of_jobs = config().number_of_jobs();

  // Total number of boxes that are either 1) under processing in a worker or 2)
  // waiting for a worker in the stack. This number goes zero when there is no
  // more work to do.
  atomic<int> number_of_boxes{0};

  global_stack.push(cs->box());
  ++number_of_boxes;

  for (int i = 0; i < number_of_jobs; ++i) {
    status_vector_.push_back(*cs);
  }

  for (int i = 0; i < number_of_jobs - 1; ++i) {
    results_.push_back(
        pool_.enqueue(Worker, contractor, config(), formula_evaluators, i,
                      false /* not main thread */, &global_stack,
                      &status_vector_[i], &found_delta_sat, &number_of_boxes));
  }

  const int last_index{number_of_jobs - 1};
  Worker(contractor, config(), formula_evaluators, last_index,
         true /* main thread */, &global_stack, &status_vector_[last_index],
         &found_delta_sat, &number_of_boxes);

  // barrier.
  for (auto&& result : results_) {
    result.get();
  }

  // Post-processing: Join all the contractor statuses.
  for (const auto& cs_i : status_vector_) {
    cs->InplaceJoin(cs_i);
  }

  if (found_delta_sat >= 0) {
    cs->mutable_box() = status_vector_[found_delta_sat].box();
    return true;
  } else {
    DREAL_ASSERT(found_delta_sat == -1);
    cs->mutable_box().set_empty();
    return false;
  }
}
}  // namespace dreal
