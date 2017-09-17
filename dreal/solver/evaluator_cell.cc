#include "dreal/solver/evaluator_cell.h"

#include <utility>

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::make_pair;
using std::ostream;
using std::pair;
using std::vector;

namespace {

// Decomposes a formula `f = e₁ rop e₂` into `(rop, e₁ - e₂)`.
pair<RelationalOperator, Expression> Decompose(const Formula& f) {
  switch (f.get_kind()) {
    case FormulaKind::Eq:
      return make_pair(RelationalOperator::EQ,
                       get_lhs_expression(f) - get_rhs_expression(f));

    case FormulaKind::Neq:
      return make_pair(RelationalOperator::NEQ,
                       get_lhs_expression(f) - get_rhs_expression(f));

    case FormulaKind::Gt:
      return make_pair(RelationalOperator::GT,
                       get_lhs_expression(f) - get_rhs_expression(f));

    case FormulaKind::Geq:
      return make_pair(RelationalOperator::GEQ,
                       get_lhs_expression(f) - get_rhs_expression(f));

    case FormulaKind::Lt:
      return make_pair(RelationalOperator::LT,
                       get_lhs_expression(f) - get_rhs_expression(f));

    case FormulaKind::Leq:
      return make_pair(RelationalOperator::LEQ,
                       get_lhs_expression(f) - get_rhs_expression(f));

    case FormulaKind::Not: {
      const pair<RelationalOperator, Expression> result{
          Decompose(get_operand(f))};
      return make_pair(!result.first, result.second);
    }

    case FormulaKind::True:
    case FormulaKind::False:
    case FormulaKind::And:
    case FormulaKind::Or:
    case FormulaKind::Forall:
    case FormulaKind::Var:
      throw std::runtime_error("should not be reachable");
  }
  throw std::runtime_error("should not be reachable");
}
}  // namespace

EvaluatorQuantifierFree::EvaluatorQuantifierFree(
    const Formula& f, const vector<Variable>& variables)
    : ibex_converter_{new IbexConverter{variables}} {
  const pair<RelationalOperator, Expression> result{Decompose(f)};
  op_ = result.first;
  func_.reset(new ibex::Function(ibex_converter_->variables(),
                                 *ibex_converter_->Convert(result.second)));
  assert(func_);
}

EvaluationResult EvaluatorQuantifierFree::operator()(const Box& box) const {
  assert(func_);
  const Box::Interval evaluation{func_->eval(box.interval_vector())};
  switch (op_) {
    case RelationalOperator::EQ: {
      // e₁ - e₂ = 0
      // VALID if e₁ - e₂ == [0, 0].
      if (evaluation.lb() == 0.0 && evaluation.ub() == 0.0) {
        return EvaluationResult{EvaluationResult::Type::VALID, evaluation};
      }
      // UNSAT if 0 ∉ e₁ - e₂
      if (!evaluation.contains(0.0)) {
        return EvaluationResult{EvaluationResult::Type::UNSAT, evaluation};
      }
      // Otherwise, it's UNKNOWN. It should be the case that 0.0 ∈ e₁ - e₂.
      return EvaluationResult{EvaluationResult::Type::UNKNOWN, evaluation};
    }

    case RelationalOperator::NEQ: {
      // e₁ - e₂ ≠ 0
      // VALID if 0.0 ∉ e₁ - e₂
      if (evaluation.ub() < 0.0 || evaluation.lb() > 0.0) {
        return EvaluationResult{EvaluationResult::Type::VALID, evaluation};
      }
      // UNSAT if e₁ - e₂ = 0.0
      if (evaluation.ub() == 0.0 && evaluation.lb() == 0.0) {
        return EvaluationResult{EvaluationResult::Type::UNSAT, evaluation};
      }
      // Otherwise, it's UNKNOWN. It should be the case that 0.0 ∈ e₁ - e₂.
      return EvaluationResult{EvaluationResult::Type::UNKNOWN, evaluation};
    }

    case RelationalOperator::GT: {
      // e₁ - e₂ > 0
      // VALID if e₁ - e₂ > 0.
      if (evaluation.lb() > 0.0) {
        return EvaluationResult{EvaluationResult::Type::VALID, evaluation};
      }
      // UNSAT if e₁ - e₂ ≤ 0.
      if (evaluation.ub() <= 0.0) {
        return EvaluationResult{EvaluationResult::Type::UNSAT, evaluation};
      }
      // Otherwise, it's UNKNOWN.
      return EvaluationResult{EvaluationResult::Type::UNKNOWN, evaluation};
    }

    case RelationalOperator::GEQ: {
      // e₁ - e₂ ≥ 0
      // VALID if e₁ - e₂ ≥ 0.
      if (evaluation.lb() >= 0.0) {
        return EvaluationResult{EvaluationResult::Type::VALID, evaluation};
      }
      // UNSAT if e₁ - e₂ < 0.
      if (evaluation.ub() < 0.0) {
        return EvaluationResult{EvaluationResult::Type::UNSAT, evaluation};
      }
      // Otherwise, it's UNKNOWN.
      return EvaluationResult{EvaluationResult::Type::UNKNOWN, evaluation};
    }

    case RelationalOperator::LT: {
      // e₁ - e₂ < 0
      // VALID if e₁ - e₂ < 0.
      if (evaluation.ub() < 0.0) {
        return EvaluationResult{EvaluationResult::Type::VALID, evaluation};
      }
      // UNSAT if e₁ - e₂ ≥ 0.
      if (evaluation.lb() >= 0.0) {
        return EvaluationResult{EvaluationResult::Type::UNSAT, evaluation};
      }
      // Otherwise, it's UNKNOWN.
      return EvaluationResult{EvaluationResult::Type::UNKNOWN, evaluation};
    }

    case RelationalOperator::LEQ: {
      // e₁ - e₂ ≤ 0
      // VALID if e₁ - e₂ ≤ 0.
      if (evaluation.ub() <= 0.0) {
        return EvaluationResult{EvaluationResult::Type::VALID, evaluation};
      }
      // UNSAT if e₁ - e₂ > 0.
      if (evaluation.lb() > 0.0) {
        return EvaluationResult{EvaluationResult::Type::UNSAT, evaluation};
      }
      // Otherwise, it's UNKNOWN.
      return EvaluationResult{EvaluationResult::Type::UNKNOWN, evaluation};
    }
  }
  throw std::runtime_error("should not be reachable");
}

ostream& EvaluatorQuantifierFree::Display(ostream& os) const {
  assert(func_);
  return os << "Evaluator(" << func_->expr() << " " << op_ << " 0.0)";
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
  context_.mutable_config().mutable_precision() = delta;
  for (const Variable& exist_var : variables) {
    context_.DeclareVariable(exist_var);
  }
  for (const Variable& forall_var : get_quantified_variables(f)) {
    context_.DeclareVariable(forall_var);
  }
  context_.Assert(DeltaStrengthen(!get_quantified_formula(f), delta * 1.1));
}

EvaluationResult EvaluatorForall::operator()(const Box& box) const {
  for (const Variable& v : box.variables()) {
    context_.SetInterval(v, box[v].lb(), box[v].ub());
  }
  const auto result = context_.CheckSat();
  DREAL_LOG_DEBUG("EvaluatorForall::operator({})", box);
  if (result) {
    DREAL_LOG_DEBUG("EvaluatorForall::operator()  --  CE found: ", *result);
    return EvaluationResult{EvaluationResult::Type::UNKNOWN,
                            Box::Interval(0.0, delta_ * 1.1)};

  } else {
    DREAL_LOG_DEBUG("EvaluatorForall::operator()  --  No CE found: ");
    return EvaluationResult{EvaluationResult::Type::VALID,
                            Box::Interval(0.0, 0.0)};
  }
}

ostream& EvaluatorForall::Display(ostream& os) const {
  return os << "Evaluator(" << f_ << ")";
}

}  // namespace dreal
