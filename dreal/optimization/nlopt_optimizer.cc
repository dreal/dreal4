#include "dreal/optimization/nlopt_optimizer.h"

#include <cmath>
#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/exception.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::make_unique;
using std::move;
using std::ostream;
using std::vector;

namespace {
/// A function passed to nlopt (type = nlopt_func). Given a vector @p
/// x, returns the evaluation of @p f_data at @p x and updates @p grad
/// which is the gradient of the function @p f_data with respect to @p
/// x.
///
/// @see
/// http://nlopt.readthedocs.io/en/latest/NLopt_Reference/#objective-function.
double NloptOptimizerEvaluate(const unsigned n, const double* x, double* grad,
                              void* const f_data) {
  DREAL_ASSERT(f_data);
  auto& expression = *static_cast<CachedExpression*>(f_data);
  const Box& box{expression.box()};
  DREAL_ASSERT(n == static_cast<size_t>(box.size()));
  DREAL_ASSERT(n > 0);
  // Set up an environment.
  Environment& env{expression.mutable_environment()};
  for (size_t i = 0; i < n; ++i) {
    const Variable& var{box.variable(i)};
    if (std::isnan(x[i])) {
      throw DREAL_RUNTIME_ERROR(
          "NloptOptimizer: x[{}] = nan is detected during evaluation", i);
    }
    env[var] = x[i];
  }
  // Set up gradients.
  if (grad) {
    for (int i = 0; i < box.size(); ++i) {
      const Variable& var{box.variable(i)};
      grad[i] = expression.Differentiate(var).Evaluate(env);
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
NloptOptimizer::NloptOptimizer(const nlopt::algorithm algorithm, Box bound,
                               const Config& config)
    : opt_{algorithm, static_cast<unsigned>(bound.size())},
      box_{move(bound)},
      delta_{config.precision()} {
  DREAL_ASSERT(delta_ > 0.0);
  DREAL_LOG_DEBUG("NloptOptimizer::NloptOptimizer: Box = \n{}", box_);

  // Set tolerance.
  opt_.set_ftol_rel(config.nlopt_ftol_rel());
  opt_.set_ftol_abs(config.nlopt_ftol_abs());
  opt_.set_maxeval(config.nlopt_maxeval());
  opt_.set_maxtime(config.nlopt_maxtime());
  DREAL_LOG_DEBUG("NloptOptimizer::NloptOptimizer: ftol_rel = {}",
                  config.nlopt_ftol_rel());
  DREAL_LOG_DEBUG("NloptOptimizer::NloptOptimizer: ftol_abs = {}",
                  config.nlopt_ftol_abs());
  DREAL_LOG_DEBUG("NloptOptimizer::NloptOptimizer: maxeval = {}",
                  config.nlopt_maxeval());
  DREAL_LOG_DEBUG("NloptOptimizer::NloptOptimizer: maxtime = {}",
                  config.nlopt_maxtime());

  // Set bounds.
  vector<double> lower_bounds(box_.size(), 0.0);
  vector<double> upper_bounds(box_.size(), 0.0);
  for (int i = 0; i < box_.size(); ++i) {
    lower_bounds[i] = box_[i].lb();
    upper_bounds[i] = box_[i].ub();
    DREAL_LOG_DEBUG("NloptOptimizer::NloptOptimizer {} ∈ [{}, {}]",
                    box_.variable(i), lower_bounds[i], upper_bounds[i]);
  }
  opt_.set_lower_bounds(lower_bounds);
  opt_.set_upper_bounds(upper_bounds);
}

void NloptOptimizer::SetMinObjective(const Expression& objective) {
  DREAL_LOG_DEBUG("NloptOptimizer::SetMinObjective({})", objective);
  objective_ = CachedExpression{objective, box_};
  opt_.set_min_objective(NloptOptimizerEvaluate,
                         static_cast<void*>(&objective_));
}

void NloptOptimizer::AddConstraint(const Formula& formula) {
  DREAL_LOG_DEBUG("NloptOptimizer::AddConstraint({})", formula);
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
  throw DREAL_RUNTIME_ERROR(
      "NloptOptimizer::AddConstraint: Unsupported formula {}.", formula);
}

void NloptOptimizer::AddRelationalConstraint(const Formula& formula) {
  DREAL_ASSERT(is_relational(formula));
  DREAL_LOG_DEBUG("NloptOptimizer::AddRelationalconstraint({})", formula);
  bool equality{false};
  if (is_greater_than(formula) || is_greater_than_or_equal_to(formula)) {
    // f := e₁ > e₂  –>  e₂ - e₁ < 0.
    const Expression& e1{get_lhs_expression(formula)};
    const Expression& e2{get_rhs_expression(formula)};
    auto cached_expression = make_unique<CachedExpression>(e2 - e1, box_);
    constraints_.push_back(move(cached_expression));
  } else if (is_less_than(formula) || is_less_than_or_equal_to(formula)) {
    // f := e₁ < e₂  –>  e₁ - e₂ < 0.
    const Expression& e1{get_lhs_expression(formula)};
    const Expression& e2{get_rhs_expression(formula)};
    auto cached_expression = make_unique<CachedExpression>(e1 - e2, box_);
    constraints_.push_back(move(cached_expression));
  } else if (is_equal_to(formula)) {
    // f := e₁ == e₂  -> e₁ - e₂ == 0
    auto cached_expression = make_unique<CachedExpression>(
        get_lhs_expression(formula) - get_rhs_expression(formula), box_);
    constraints_.push_back(move(cached_expression));
    equality = true;
  } else {
    throw DREAL_RUNTIME_ERROR(
        "NloptOptimizer::AddRelationalConstraint: Unsupported formula {}.",
        formula);
  }

  if (equality) {
    opt_.add_equality_constraint(NloptOptimizerEvaluate,
                                 static_cast<void*>(constraints_.back().get()),
                                 delta_);
  } else {
    opt_.add_inequality_constraint(
        &NloptOptimizerEvaluate, static_cast<void*>(constraints_.back().get()),
        delta_);
  }
}

void NloptOptimizer::AddConstraints(const vector<Formula>& formulas) {
  for (const Formula& formula : formulas) {
    AddConstraint(formula);
  }
}

nlopt::result NloptOptimizer::Optimize(vector<double>* const x,
                                       double* const opt_f) {
  return opt_.optimize(*x, *opt_f);
}

nlopt::result NloptOptimizer::Optimize(vector<double>* const x,
                                       double* const opt_f,
                                       const Environment& env) {
  // Update objective_ and constraints_ with env.
  objective_.mutable_environment() = env;
  for (auto& constraint_ptr : constraints_) {
    constraint_ptr->mutable_environment() = env;
  }
  return Optimize(x, opt_f);
}

}  // namespace dreal
