#include "dreal/solver/evaluator.h"

#include <utility>

#include "dreal/solver/evaluator_cell.h"
#include "dreal/solver/evaluator_forall.h"
#include "dreal/solver/evaluator_quantifier_free.h"
#include "dreal/util/exception.h"

namespace dreal {

using std::make_shared;
using std::move;
using std::ostream;
using std::shared_ptr;
using std::vector;

EvaluationResult::EvaluationResult(Type type, Box::Interval evaluation)
    : type_{type}, evaluation_{std::move(evaluation)} {}

EvaluationResult::Type EvaluationResult::type() const { return type_; }

const Box::Interval& EvaluationResult::evaluation() const {
  return evaluation_;
}

ostream& operator<<(ostream& os, EvaluationResult::Type type) {
  switch (type) {
    case EvaluationResult::Type::VALID:
      return os << "VALID";
    case EvaluationResult::Type::UNSAT:
      return os << "UNSAT";
    case EvaluationResult::Type::UNKNOWN:
      return os << "UNKNOWN";
  }
  DREAL_UNREACHABLE();
}

ostream& operator<<(ostream& os, const EvaluationResult& result) {
  return os << "[" << result.type() << ", " << result.evaluation() << "]";
}

Evaluator::Evaluator(shared_ptr<EvaluatorCell> ptr) : ptr_{move(ptr)} {}

EvaluationResult Evaluator::operator()(const Box& box) const {
  return (*ptr_)(box);
}

ostream& operator<<(ostream& os, const Evaluator& evaluator) {
  return evaluator.ptr_->Display(os);
}

Evaluator make_evaluator_quantifier_free(
    const Formula& f, const std::vector<Variable>& variables) {
  assert(!is_forall(f));
  return Evaluator{make_shared<EvaluatorQuantifierFree>(f, variables)};
}

Evaluator make_evaluator_forall(const Formula& f,
                                const std::vector<Variable>& variables,
                                const double epsilon, const double delta) {
  assert(is_forall(f));
  return Evaluator{make_shared<EvaluatorForall>(f, variables, epsilon, delta)};
}

}  // namespace dreal
