#include "dreal/solver/relational_formula_evaluator.h"

#include <utility>

#include "dreal/util/exception.h"

namespace dreal {

using std::make_pair;
using std::make_shared;
using std::move;
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
      DREAL_UNREACHABLE();
    case FormulaKind::False:
      DREAL_UNREACHABLE();
    case FormulaKind::And:
      DREAL_UNREACHABLE();
    case FormulaKind::Or:
      DREAL_UNREACHABLE();
    case FormulaKind::Forall:
      DREAL_UNREACHABLE();
    case FormulaKind::Var:
      DREAL_UNREACHABLE();
  }
  DREAL_UNREACHABLE();
}
}  // namespace

RelationalFormulaEvaluator::RelationalFormulaEvaluator(
    const RelationalOperator op, ExpressionEvaluator expression_evaluator)
    : op_{op}, expression_evaluator_{move(expression_evaluator)} {}

RelationalFormulaEvaluator RelationalFormulaEvaluator::Make(
    const Formula& f, const vector<Variable>& variables) {
  assert(is_relational(f) || (is_negation(f) && is_relational(get_operand(f))));
  const pair<RelationalOperator, Expression> result{Decompose(f)};
  return RelationalFormulaEvaluator{
      result.first, ExpressionEvaluator{result.second, variables}};
}

RelationalFormulaEvaluator::~RelationalFormulaEvaluator() {
  DREAL_LOG_DEBUG("RelationalFormulaEvaluator::~RelationalFormulaEvaluator()");
}

FormulaEvaluationResult RelationalFormulaEvaluator::operator()(
    const Box& box) const {
  const Box::Interval evaluation{expression_evaluator_(box)};
  switch (op_) {
    case RelationalOperator::EQ: {
      // e₁ - e₂ = 0
      // VALID if e₁ - e₂ == [0, 0].
      if (evaluation.lb() == 0.0 && evaluation.ub() == 0.0) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::VALID,
                                       evaluation};
      }
      // UNSAT if 0 ∉ e₁ - e₂
      if (!evaluation.contains(0.0)) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNSAT,
                                       evaluation};
      }
      // Otherwise, it's UNKNOWN. It should be the case that 0.0 ∈ e₁ - e₂.
      return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNKNOWN,
                                     evaluation};
    }

    case RelationalOperator::NEQ: {
      // e₁ - e₂ ≠ 0
      // VALID if 0.0 ∉ e₁ - e₂
      if (evaluation.ub() < 0.0 || evaluation.lb() > 0.0) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::VALID,
                                       evaluation};
      }
      // UNSAT if e₁ - e₂ = 0.0
      if (evaluation.ub() == 0.0 && evaluation.lb() == 0.0) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNSAT,
                                       evaluation};
      }
      // Otherwise, it's UNKNOWN. It should be the case that 0.0 ∈ e₁ - e₂.
      return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNKNOWN,
                                     evaluation};
    }

    case RelationalOperator::GT: {
      // e₁ - e₂ > 0
      // VALID if e₁ - e₂ > 0.
      if (evaluation.lb() > 0.0) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::VALID,
                                       evaluation};
      }
      // UNSAT if e₁ - e₂ ≤ 0.
      if (evaluation.ub() <= 0.0) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNSAT,
                                       evaluation};
      }
      // Otherwise, it's UNKNOWN.
      return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNKNOWN,
                                     evaluation};
    }

    case RelationalOperator::GEQ: {
      // e₁ - e₂ ≥ 0
      // VALID if e₁ - e₂ ≥ 0.
      if (evaluation.lb() >= 0.0) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::VALID,
                                       evaluation};
      }
      // UNSAT if e₁ - e₂ < 0.
      if (evaluation.ub() < 0.0) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNSAT,
                                       evaluation};
      }
      // Otherwise, it's UNKNOWN.
      return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNKNOWN,
                                     evaluation};
    }

    case RelationalOperator::LT: {
      // e₁ - e₂ < 0
      // VALID if e₁ - e₂ < 0.
      if (evaluation.ub() < 0.0) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::VALID,
                                       evaluation};
      }
      // UNSAT if e₁ - e₂ ≥ 0.
      if (evaluation.lb() >= 0.0) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNSAT,
                                       evaluation};
      }
      // Otherwise, it's UNKNOWN.
      return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNKNOWN,
                                     evaluation};
    }

    case RelationalOperator::LEQ: {
      // e₁ - e₂ ≤ 0
      // VALID if e₁ - e₂ ≤ 0.
      if (evaluation.ub() <= 0.0) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::VALID,
                                       evaluation};
      }
      // UNSAT if e₁ - e₂ > 0.
      if (evaluation.lb() > 0.0) {
        return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNSAT,
                                       evaluation};
      }
      // Otherwise, it's UNKNOWN.
      return FormulaEvaluationResult{FormulaEvaluationResult::Type::UNKNOWN,
                                     evaluation};
    }
  }
  DREAL_UNREACHABLE();
}

ostream& RelationalFormulaEvaluator::Display(ostream& os) const {
  return os << "FormulaEvaluator(" << *(expression_evaluator_.func_) << " "
            << op_ << " 0.0)";
}
}  // namespace dreal
