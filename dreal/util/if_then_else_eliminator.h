#pragma once

#include <unordered_set>
#include <vector>

#include "dreal/symbolic/symbolic.h"

namespace dreal {

/// Eliminates If-Then-Else expressions by introducing new variables.
///
/// TODO(soonho): Check "Efficient Term ITE Conversion for
/// Satisfiability Modulo Theories", H. Kim, F. Somenzi,
/// H. Jin. Twelfth International Conference on Theory and
/// Applications of Satisfiability Testing (SAT'09).
class IfThenElseEliminator {
 public:
  /// Returns a equisatisfiable formula by eliminating
  /// if-then-expressions in @p f by introducing new variables.
  Formula Process(const Formula& f);
  const std::unordered_set<Variable, hash_value<Variable>>& variables() const;

 private:
  // Handle expressions.
  Expression Visit(const Expression& e);
  Expression VisitVariable(const Expression& e);
  Expression VisitConstant(const Expression& e);
  Expression VisitRealConstant(const Expression& e);
  Expression VisitAddition(const Expression& e);
  Expression VisitMultiplication(const Expression& e);
  Expression VisitDivision(const Expression& e);
  Expression VisitLog(const Expression& e);
  Expression VisitAbs(const Expression& e);
  Expression VisitExp(const Expression& e);
  Expression VisitSqrt(const Expression& e);
  Expression VisitPow(const Expression& e);
  Expression VisitSin(const Expression& e);
  Expression VisitCos(const Expression& e);
  Expression VisitTan(const Expression& e);
  Expression VisitAsin(const Expression& e);
  Expression VisitAcos(const Expression& e);
  Expression VisitAtan(const Expression& e);
  Expression VisitAtan2(const Expression& e);
  Expression VisitSinh(const Expression& e);
  Expression VisitCosh(const Expression& e);
  Expression VisitTanh(const Expression& e);
  Expression VisitMin(const Expression& e);
  Expression VisitMax(const Expression& e);
  Expression VisitIfThenElse(const Expression& e);
  Expression VisitUninterpretedFunction(const Expression& e);

  // Handle formula
  Formula Visit(const Formula& f);
  Formula VisitFalse(const Formula& f);
  Formula VisitTrue(const Formula& f);
  Formula VisitVariable(const Formula& f);
  Formula VisitEqualTo(const Formula& f);
  Formula VisitNotEqualTo(const Formula& f);
  Formula VisitGreaterThan(const Formula& f);
  Formula VisitGreaterThanOrEqualTo(const Formula& f);
  Formula VisitLessThan(const Formula& f);
  Formula VisitLessThanOrEqualTo(const Formula& f);
  Formula VisitConjunction(const Formula& f);
  Formula VisitDisjunction(const Formula& f);
  Formula VisitNegation(const Formula& f);
  Formula VisitForall(const Formula& f);

  // ---------------
  // Member fields
  // ---------------

  // The added formulas introduced by the elimination process.
  std::vector<Formula> added_formulas_;
  // The variables introduced by the elimination process.
  std::unordered_set<Variable, hash_value<Variable>> ite_variables_;

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula>(IfThenElseEliminator*,
                                                        const Formula&);
  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend Expression drake::symbolic::VisitExpression<Expression>(
      IfThenElseEliminator*, const Expression&);
};
}  // namespace dreal
