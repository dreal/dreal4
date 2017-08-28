#include "dreal/util/evaluator.h"

namespace dreal {

using std::make_shared;
using std::ostream;
using std::vector;

Evaluator::Evaluator(const Formula& f, const vector<Variable>& variables)
    : ibex_converter_{new IbexConverter{variables}},
      expr_ctr_{ibex_converter_->Convert(f)} {
  if (expr_ctr_) {
    func_.reset(new ibex::Function(ibex_converter_->variables(), expr_ctr_->e));
  }
}

Box::Interval Evaluator::Eval(const Box& box) const {
  if (func_) {
    return func_->eval(box.interval_vector());
  } else {
    return Box::Interval(0.0, 0.0);
  }
}

ostream& operator<<(ostream& os, const Evaluator& evaluator) {
  if (evaluator.func_) {
    return os << evaluator.func_->expr();
  } else {
    return os << "uninitialized function";
  }
}

}  // namespace dreal
