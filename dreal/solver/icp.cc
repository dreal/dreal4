#include "dreal/solver/icp.h"

#include <ostream>
#include <tuple>
#include <utility>

#include "dreal/util/logging.h"

using std::vector;

namespace dreal {

Icp::Icp(const Config& config) : config_{config} {}

optional<ibex::BitSet> EvaluateBox(
    const vector<FormulaEvaluator>& formula_evaluators, const Box& box,
    const double precision, ContractorStatus* const cs) {
  ibex::BitSet branching_candidates(box.size());  // This function returns this.
  for (const FormulaEvaluator& formula_evaluator : formula_evaluators) {
    const FormulaEvaluationResult result{formula_evaluator(box)};
    switch (result.type()) {
      case FormulaEvaluationResult::Type::UNSAT:
        DREAL_LOG_DEBUG(
            "Icp::EvaluateBox() Found that the box\n"
            "{0}\n"
            "has no solution for {1} (evaluation = {2}).",
            box, formula_evaluator, result.evaluation());
        cs->mutable_box().set_empty();
        cs->AddUsedConstraint(formula_evaluator.formula());
        return nullopt;
      case FormulaEvaluationResult::Type::VALID:
        DREAL_LOG_DEBUG(
            "Icp::EvaluateBox() Found that all points in the box\n"
            "{0}\n"
            "satisfies the constraint {1} (evaluation = {2}).",
            box, formula_evaluator, result.evaluation());
        continue;
      case FormulaEvaluationResult::Type::UNKNOWN: {
        const Box::Interval& evaluation{result.evaluation()};
        const double diam = evaluation.diam();
        if (diam > precision) {
          DREAL_LOG_DEBUG(
              "Icp::EvaluateBox() Found an interval >= precision({2}):\n"
              "{0} -> {1}",
              formula_evaluator, evaluation, precision);
          for (const Variable& v : formula_evaluator.variables()) {
            branching_candidates.add(box.index(v));
          }
        }
        break;
      }
    }
  }
  return branching_candidates;
}

}  // namespace dreal
