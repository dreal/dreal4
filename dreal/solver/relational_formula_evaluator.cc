#include "dreal/solver/relational_formula_evaluator.h"

#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/exception.h"

namespace dreal {

using std::move;
using std::ostream;

namespace {

RelationalOperator GetRelationalOperator(const Formula& f) {
  DREAL_ASSERT(is_relational(f) || is_negation(f));
  switch (f.get_kind()) {
    case FormulaKind::Eq:
      return RelationalOperator::EQ;

    case FormulaKind::Neq:
      return RelationalOperator::NEQ;

    case FormulaKind::Gt:
      return RelationalOperator::GT;

    case FormulaKind::Geq:
      return RelationalOperator::GEQ;

    case FormulaKind::Lt:
      return RelationalOperator::LT;

    case FormulaKind::Leq:
      return RelationalOperator::LEQ;

    case FormulaKind::Not:
      return !GetRelationalOperator(get_operand(f));

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

// Decomposes a formula `f = e₁ rop e₂` into `(rop, e₁ - e₂)`.
Expression ExtractExpression(const Formula& f) {
  if (is_relational(f)) {
    return get_lhs_expression(f) - get_rhs_expression(f);
  } else {
    DREAL_ASSERT(is_negation(f));
    return ExtractExpression(get_operand(f));
  }
}
}  // namespace

RelationalFormulaEvaluator::RelationalFormulaEvaluator(Formula f)
    : FormulaEvaluatorCell{move(f)},
      op_{GetRelationalOperator(formula())},
      expression_evaluator_{ExtractExpression(formula())} {}

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
  return os << "RelationalFormulaEvaluator(" << expression_evaluator_ << " "
            << op_ << " 0.0)";
}
}  // namespace dreal
