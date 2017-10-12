#include "dreal/solver/formula_evaluator.h"

#include <utility>

#include "dreal/solver/forall_formula_evaluator.h"
#include "dreal/solver/formula_evaluator_cell.h"
#include "dreal/solver/relational_formula_evaluator.h"
#include "dreal/util/exception.h"

namespace dreal {

using std::make_shared;
using std::move;
using std::ostream;
using std::shared_ptr;
using std::vector;

FormulaEvaluationResult::FormulaEvaluationResult(Type type,
                                                 Box::Interval evaluation)
    : type_{type}, evaluation_{std::move(evaluation)} {}

FormulaEvaluationResult::Type FormulaEvaluationResult::type() const {
  return type_;
}

const Box::Interval& FormulaEvaluationResult::evaluation() const {
  return evaluation_;
}

ostream& operator<<(ostream& os, FormulaEvaluationResult::Type type) {
  switch (type) {
    case FormulaEvaluationResult::Type::VALID:
      return os << "VALID";
    case FormulaEvaluationResult::Type::UNSAT:
      return os << "UNSAT";
    case FormulaEvaluationResult::Type::UNKNOWN:
      return os << "UNKNOWN";
  }
  DREAL_UNREACHABLE();
}

ostream& operator<<(ostream& os, const FormulaEvaluationResult& result) {
  return os << "[" << result.type() << ", " << result.evaluation() << "]";
}

FormulaEvaluator::FormulaEvaluator(shared_ptr<FormulaEvaluatorCell> ptr)
    : ptr_{move(ptr)} {}

FormulaEvaluationResult FormulaEvaluator::operator()(const Box& box) const {
  return (*ptr_)(box);
}

ostream& operator<<(ostream& os, const FormulaEvaluator& evaluator) {
  return evaluator.ptr_->Display(os);
}

FormulaEvaluator make_relational_formula_evaluator(
    const Formula& f, const std::vector<Variable>& variables) {
  assert(!is_forall(f));
  return FormulaEvaluator{
      make_shared<RelationalFormulaEvaluator>(f, variables)};
}

FormulaEvaluator make_forall_formula_evaluator(
    const Formula& f, const std::vector<Variable>& variables,
    const double epsilon, const double delta) {
  assert(is_forall(f));
  return FormulaEvaluator{
      make_shared<ForallFormulaEvaluator>(f, variables, epsilon, delta)};
}

}  // namespace dreal
