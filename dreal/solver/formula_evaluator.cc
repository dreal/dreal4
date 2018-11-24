#include "dreal/solver/formula_evaluator.h"

#include <cassert>
#include <utility>

#include "dreal/solver/expression_evaluator.h"
#include "dreal/solver/forall_formula_evaluator.h"
#include "dreal/solver/formula_evaluator_cell.h"
#include "dreal/solver/relational_formula_evaluator.h"
#include "dreal/util/assert.h"
#include "dreal/util/exception.h"

namespace dreal {

using std::make_shared;
using std::move;
using std::ostream;
using std::shared_ptr;

FormulaEvaluationResult::FormulaEvaluationResult(Type type,
                                                 Box::Interval evaluation)
    : type_{type}, evaluation_{evaluation} {}

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

FormulaEvaluator::FormulaEvaluator(std::shared_ptr<FormulaEvaluatorCell> ptr)
    : ptr_{move(ptr)} {
  DREAL_ASSERT(ptr_);
}

FormulaEvaluationResult FormulaEvaluator::operator()(const Box& box) const {
  return (*ptr_)(box);
}

const Variables& FormulaEvaluator::variables() const {
  return ptr_->variables();
}

const Formula& FormulaEvaluator::formula() const { return ptr_->formula(); }

ostream& operator<<(ostream& os, const FormulaEvaluator& evaluator) {
  return evaluator.ptr_->Display(os);
}

FormulaEvaluator make_relational_formula_evaluator(const Formula& f) {
  return FormulaEvaluator{make_shared<RelationalFormulaEvaluator>(f)};
}

FormulaEvaluator make_forall_formula_evaluator(const Formula& f,
                                               const double epsilon,
                                               const double delta) {
  DREAL_ASSERT(is_forall(f));
  return FormulaEvaluator{
      make_shared<ForallFormulaEvaluator>(f, epsilon, delta)};
}

}  // namespace dreal
