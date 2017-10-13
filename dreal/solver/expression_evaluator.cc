#include "dreal/solver/expression_evaluator.h"

namespace dreal {

using std::make_shared;
using std::vector;

ExpressionEvaluator::ExpressionEvaluator(const Expression& e,
                                         const vector<Variable>& variables)
    : ibex_converter_{make_shared<IbexConverter>(variables)} {
  func_ = make_shared<ibex::Function>(ibex_converter_->variables(),
                                      *ibex_converter_->Convert(e));
  assert(func_);
}

ExpressionEvaluator::ExpressionEvaluator(const Expression& e, const Box& box)
    : ExpressionEvaluator{e, box.variables()} {}

/// Evaluates the expression with @p box.
Box::Interval ExpressionEvaluator::operator()(const Box& box) const {
  return func_->eval(box.interval_vector());
}

double ExpressionEvaluator::EvaluateAtCenter(const Box& box) const {
  return func_->eval(box.interval_vector().mid()).mid();
}

std::ostream& operator<<(std::ostream& os,
                         const ExpressionEvaluator& expression_evaluator) {
  return os << "ExpressionEvaluator(" << *(expression_evaluator.func_) << ")";
}

}  // namespace dreal
