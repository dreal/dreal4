#include "dreal/solver/icp.h"

#include <utility>

#include "dreal/util/logging.h"

using std::move;
using std::pair;
using std::vector;

namespace dreal {

Icp::Icp(Contractor contractor, vector<Evaluator> evaluators,
         const double precision)
    : contractor_{move(contractor)},
      evaluators_{move(evaluators)},
      precision_{precision} {}

bool Icp::CheckSat(ContractorStatus* cs) {
  DREAL_LOG_DEBUG("Icp::CheckSat()");
  vector<Box> stack;
  stack.push_back(cs->box());

  // `current_box` always points to the box in the cs by reference.
  Box& current_box{cs->get_mutable_box()};

  bool flip = false;  // To decide which box to add first after branching.
  while (!stack.empty()) {
    // Pop the current box from the stack
    current_box = stack.back();
    stack.pop_back();
    DREAL_LOG_TRACE("Icp::CheckSat() Current Box:\n{}", current_box);
    contractor_.Prune(cs);
    if (current_box.empty()) {
      // Nothing to do.
      DREAL_LOG_TRACE("Icp::CheckSat() Box is empty after pruning");
    } else {
      DREAL_LOG_TRACE("Icp::CheckSat() After pruning, the current box =\n{}",
                      current_box);

      // Evaluate each assertion fᵢ with the current box, B. Stop the ICP
      // loop if |fᵢ(B)| ≤ δ for all fᵢ.
      bool delta_check = true;
      for (const Evaluator& evaluator : evaluators_) {
        const EvaluationResult result{evaluator(current_box)};
        const Box::Interval& evaluation{result.evaluation()};
        if (evaluation.diam() > precision_) {
          DREAL_LOG_DEBUG(
              "Icp::CheckSat() Found an interval >= precision({2}):\n{0} -> "
              "{1}",
              evaluator, evaluation, precision_);
          delta_check = false;
          break;
        }
      }
      if (delta_check) {
        // Evaluate all constraints under the current box to confirm the
        // delta-sat solution.
        bool unsat_by_evaluation{false};
        for (const Evaluator& evaluator : evaluators_) {
          const EvaluationResult result{evaluator(current_box)};
          if (result.type() == EvaluationResult::Type::UNSAT) {
            DREAL_LOG_DEBUG("Current box:\n{}\nRejected by {}", current_box,
                            evaluator);
            unsat_by_evaluation = true;
            break;
          }
        }
        if (unsat_by_evaluation) {
          current_box.set_empty();
          continue;
        } else {
          // Great, we find a box which is smaller enough!
          DREAL_LOG_DEBUG("Icp::CheckSat() Found a delta-box:\n{}",
                          current_box);
          return true;
        }
      }

      pair<double, int> max_diam_and_idx{current_box.MaxDiam()};
      const int idx_of_max_diam{max_diam_and_idx.second};
      if (idx_of_max_diam >= 0) {
        // TODO(soonho): For now, we fixated the branching heuristics.
        // Generalize it later.
        const pair<Box, Box> bisected_boxes{
            current_box.bisect(idx_of_max_diam)};

        // TODO(soonho): For now, we fixated the order here. Generalize it
        // later.
        if (flip) {
          stack.push_back(bisected_boxes.first);
          stack.push_back(bisected_boxes.second);
        } else {
          stack.push_back(bisected_boxes.second);
          stack.push_back(bisected_boxes.first);
        }
        flip = !flip;
        DREAL_LOG_TRACE("Icp::CheckSat() Branch on {}\nBox1=\n{}\nBox2=\n{}",
                        current_box.variable(idx_of_max_diam),
                        bisected_boxes.first, bisected_boxes.second);
      } else {
        DREAL_LOG_DEBUG(
            "Icp::CheckSat() Found that the current box is not satisfying "
            "delta-condition but its not bisectable.:\n{}",
            current_box);
        return true;
      }
    }
  }
  DREAL_LOG_DEBUG("Icp::CheckSat() No solution");
  return false;
}
}  // namespace dreal
