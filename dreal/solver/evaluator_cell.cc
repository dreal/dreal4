#include "dreal/solver/evaluator_cell.h"

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::ostream;
using std::vector;

EvaluatorQuantifierFree::EvaluatorQuantifierFree(
    const Formula& f, const vector<Variable>& variables)
    : ibex_converter_{new IbexConverter{variables}},
      expr_ctr_{ibex_converter_->Convert(f)} {
  if (expr_ctr_) {
    func_.reset(new ibex::Function(ibex_converter_->variables(), expr_ctr_->e));
  }
}

Box::Interval EvaluatorQuantifierFree::operator()(const Box& box) const {
  if (func_) {
    return func_->eval(box.interval_vector());
  } else {
    return Box::Interval(0.0, 0.0);
  }
}

ostream& EvaluatorQuantifierFree::Display(ostream& os) const {
  if (func_) {
    return os << "Evaluator(" << func_->expr() << ")";
  } else {
    return os << "Evaluator(uninitialized function)";
  }
}

EvaluatorForall::EvaluatorForall(const Formula& f,
                                 const vector<Variable>& variables,
                                 const double delta)
    : f_{f}, delta_{delta} {
  DREAL_LOG_DEBUG("EvaluatorForall({})", f);
  // Given `f = ∃x.∀y.ϕ(x, y)`, we need to check if there is a
  // counterexample of f. That is, we need to check the satisfiability
  // of (¬ϕ(x, y))⁻⁽ᵟ⁺ᵉ⁾. If this is satisfiable (i.e. exists a
  // counterexample), this evaluation should return something bigger
  // than δ so that a branching will happen. If no counterexample is
  // found, it should return 0.0 so that no branching will take place
  // because of this constraint.
  context_.get_mutable_config().set_precision(delta);
  for (const Variable& exist_var : variables) {
    context_.DeclareVariable(exist_var);
  }
  for (const Variable& forall_var : get_quantified_variables(f)) {
    context_.DeclareVariable(forall_var);
  }
  context_.Assert(DeltaStrengthen(!get_quantified_formula(f), delta * 1.1));
}

Box::Interval EvaluatorForall::operator()(const Box& box) const {
  for (const Variable& v : box.variables()) {
    context_.SetInterval(v, box[v].lb(), box[v].ub());
  }
  const auto result{context_.CheckSat()};
  DREAL_LOG_DEBUG("EvaluatorForall::operator({})", box);
  if (result) {
    DREAL_LOG_DEBUG("EvaluatorForall::operator()  --  CE found: ", *result);
    return Box::Interval(0, delta_ * 1.1);
  } else {
    DREAL_LOG_DEBUG("EvaluatorForall::operator()  --  No CE found: ");
    return Box::Interval(0, 0);
  }
}

ostream& EvaluatorForall::Display(ostream& os) const {
  return os << "Evaluator(" << f_ << ")";
}

}  // namespace dreal
