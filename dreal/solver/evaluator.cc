#include "dreal/solver/evaluator.h"

#include "dreal/solver/evaluator_cell.h"

namespace dreal {

using std::make_shared;
using std::ostream;
using std::vector;

Evaluator::Evaluator(const Formula& f, const vector<Variable>& variables,
                     const double delta) {
  if (is_forall(f)) {
    ptr_ = make_shared<EvaluatorForall>(f, variables, delta);
  } else {
    ptr_ = make_shared<EvaluatorQuantifierFree>(f, variables);
  }
}

Box::Interval Evaluator::operator()(const Box& box) const {
  return (*ptr_)(box);
}

ostream& operator<<(ostream& os, const Evaluator& evaluator) {
  return evaluator.ptr_->Display(os);
}

}  // namespace dreal
