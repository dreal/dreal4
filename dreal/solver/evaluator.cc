#include "dreal/solver/evaluator.h"

#include <utility>

#include "dreal/solver/evaluator_cell.h"

namespace dreal {

using std::make_shared;
using std::move;
using std::ostream;
using std::vector;

EvaluationResult::EvaluationResult(Type type, Box::Interval evaluation)
    : type_{type}, evaluation_{std::move(evaluation)} {}

EvaluationResult::Type EvaluationResult::type() const { return type_; }

const Box::Interval& EvaluationResult::evaluation() const {
  return evaluation_;
}

Evaluator::Evaluator(const Formula& f, const vector<Variable>& variables,
                     const double delta) {
  if (is_forall(f)) {
    ptr_ = make_shared<EvaluatorForall>(f, variables, delta);
  } else {
    ptr_ = make_shared<EvaluatorQuantifierFree>(f, variables);
  }
}

EvaluationResult Evaluator::operator()(const Box& box) const {
  return (*ptr_)(box);
}

ostream& operator<<(ostream& os, const Evaluator& evaluator) {
  return evaluator.ptr_->Display(os);
}

}  // namespace dreal
