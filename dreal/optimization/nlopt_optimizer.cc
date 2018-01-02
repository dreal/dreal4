#include "dreal/optimization/nlopt_optimizer.h"

#include <sstream>
#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/exception.h"

namespace dreal {

using std::make_pair;
using std::make_unique;
using std::move;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::unique_ptr;
using std::vector;

namespace {
/// A function passed to nlopt (type = nlopt_func). Given a vector @p
/// x, returns the evaluation of @p f_data at @p x and updates @p grad
/// which is the gradient of the function @p f_data with respect to @p
/// x.
///
/// @see
/// http://nlopt.readthedocs.io/en/latest/NLopt_Reference/#objective-function.
// double NloptOptimizerEvaluate(unsigned n, const double* x, double* grad,
//                               void* f_data);
double NloptOptimizerEvaluate(const unsigned n, const double* x, double* grad,
                              void* const f_data) {
  DREAL_ASSERT(f_data);
  auto& expression = *static_cast<CachedExpression*>(f_data);
  const Box& box{expression.box()};
  DREAL_ASSERT(n == static_cast<size_t>(box.size()));
  // Set up an environment.
  Environment& env{expression.mutable_environment()};
  for (size_t i = 0; i < n; ++i) {
    const Variable& v{box.variable(i)};
    env[v] = x[i];
  }
  // Set up gradients.
  if (grad) {
    for (int i = 0; i < box.size(); ++i) {
      const Variable& v{box.variable(i)};
      grad[i] = expression.Differentiate(v).Evaluate(env);
    }
  }
  // Return evaluation.
  return expression.Evaluate(env);
}
}  // namespace

// ----------------
// CachedExpression
// ----------------
CachedExpression::CachedExpression(Expression e, const Box& box)
    : expression_{move(e)}, box_{&box} {
  DREAL_ASSERT(box_);
}

const Box& CachedExpression::box() const {
  DREAL_ASSERT(box_);
  return *box_;
}

Environment& CachedExpression::mutable_environment() { return environment_; }

const Environment& CachedExpression::environment() const {
  return environment_;
}

double CachedExpression::Evaluate(const Environment& env) const {
  return expression_.Evaluate(env);
}

const Expression& CachedExpression::Differentiate(const Variable& x) {
  auto it = gradient_.find(x);
  if (it == gradient_.end()) {
    // Not found.
    return gradient_.emplace_hint(it, x, expression_.Differentiate(x))->second;
  } else {
    return it->second;
  }
}

ostream& operator<<(ostream& os, const CachedExpression& expression) {
  return os << expression.expression_;
}

// --------------
// NloptOptimizer
// --------------
NloptOptimizer::NloptOptimizer(const nlopt_algorithm algorithm, Box bound,
                               const double delta)
    : box_{move(bound)}, delta_{delta} {
  DREAL_ASSERT(delta_ > 0.0);
  opt_ = nlopt_create(algorithm, box_.size());

  // Set tolerance.
  nlopt_set_ftol_rel(opt_, delta_);

  // Set bounds.
  const auto lower_bounds = make_unique<double[]>(box_.size());
  const auto upper_bounds = make_unique<double[]>(box_.size());
  for (int i = 0; i < box_.size(); ++i) {
    lower_bounds[i] = box_[i].lb();
    upper_bounds[i] = box_[i].ub();
  }
  const nlopt_result nlopt_result_lb{
      nlopt_set_lower_bounds(opt_, lower_bounds.get())};
  DREAL_ASSERT(nlopt_result_lb == NLOPT_SUCCESS);
  const nlopt_result nlopt_result_ub{
      nlopt_set_upper_bounds(opt_, upper_bounds.get())};
  DREAL_ASSERT(nlopt_result_ub == NLOPT_SUCCESS);
}

NloptOptimizer::~NloptOptimizer() { nlopt_destroy(opt_); }

void NloptOptimizer::SetMinObjective(const Expression& objective) {
  objective_ = CachedExpression{objective, box_};
  const nlopt_result result{nlopt_set_min_objective(
      opt_, NloptOptimizerEvaluate, static_cast<void*>(&objective_))};
  DREAL_ASSERT(result == NLOPT_SUCCESS);
}

void NloptOptimizer::AddConstraint(const Formula& formula) {
  if (is_conjunction(formula)) {
    for (const Formula& f : get_operands(formula)) {
      AddConstraint(f);
    }
    return;
  }
  if (is_relational(formula)) {
    return AddRelationalConstraint(formula);
  }
  if (is_negation(formula)) {
    const Formula& negated_formula{get_operand(formula)};
    if (is_relational(negated_formula)) {
      return AddRelationalConstraint(nnfizer_.Convert(negated_formula));
    }
  }
  ostringstream oss;
  oss << "NloptOptimizer::AddConstraint: "
      << "Unsupported formula: " << formula;
  throw DREAL_RUNTIME_ERROR(oss.str());
}

void NloptOptimizer::AddRelationalConstraint(const Formula& formula) {
  bool equality{false};
  if (is_greater_than(formula) || is_greater_than_or_equal_to(formula)) {
    // f := e₁ > e₂  –>  e₂ - e₁ < 0.
    auto cached_expression = make_unique<CachedExpression>(
        get_rhs_expression(formula) - get_lhs_expression(formula), box_);
    constraints_.push_back(move(cached_expression));
  } else if (is_less_than(formula) || is_less_than_or_equal_to(formula)) {
    // f := e₁ < e₂  –>  e₁ - e₂ < 0.
    auto cached_expression = make_unique<CachedExpression>(
        get_lhs_expression(formula) - get_rhs_expression(formula), box_);
    constraints_.push_back(move(cached_expression));
  } else if (is_equal_to(formula)) {
    // f := e₁ == e₂  -> e₁ - e₂ == 0
    auto cached_expression = make_unique<CachedExpression>(
        get_lhs_expression(formula) - get_rhs_expression(formula), box_);
    constraints_.push_back(move(cached_expression));
    equality = true;
  } else {
    ostringstream oss;
    oss << "NloptOptimizer::AddRelationalConstraint: "
        << "Unsupported formula: " << formula;
    throw DREAL_RUNTIME_ERROR(oss.str());
  }

  if (equality) {
    nlopt_add_equality_constraint(opt_, NloptOptimizerEvaluate,
                                  static_cast<void*>(constraints_.back().get()),
                                  delta_);
  } else {
    nlopt_add_inequality_constraint(
        opt_, NloptOptimizerEvaluate,
        static_cast<void*>(constraints_.back().get()), delta_);
  }
}

void NloptOptimizer::AddConstraints(const vector<Formula>& formulas) {
  for (const Formula& formula : formulas) {
    AddConstraint(formula);
  }
}

nlopt_result NloptOptimizer::Optimize(vector<double>* const x,
                                      double* const opt_f) {
  return nlopt_optimize(opt_, x->data(), opt_f);
}

}  // namespace dreal
