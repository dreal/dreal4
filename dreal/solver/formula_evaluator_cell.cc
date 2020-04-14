#include "dreal/solver/formula_evaluator_cell.h"

#include <utility>

namespace dreal {

namespace {
bool IsSimpleRelational(const Formula& f) {
  if (is_negation(f)) {
    return IsSimpleRelational(get_operand(f));
  }
  if (!is_relational(f)) {
    return false;
  }
  const Expression& lhs{get_lhs_expression(f)};
  const Expression& rhs{get_rhs_expression(f)};
  return ((is_constant(lhs) || is_real_constant(lhs)) && is_variable(rhs)) ||
         (is_variable(lhs) && (is_constant(rhs) || is_real_constant(rhs)));
}

}  // namespace

FormulaEvaluatorCell::FormulaEvaluatorCell(Formula f)
    : f_{std::move(f)}, is_simple_relational_{IsSimpleRelational(f_)} {}

}  // namespace dreal
