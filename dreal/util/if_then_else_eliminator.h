/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
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
  Expression Visit(const Expression& e, const Formula& guard);
  Expression VisitVariable(const Expression& e, const Formula& guard);
  Expression VisitConstant(const Expression& e, const Formula& guard);
  Expression VisitRealConstant(const Expression& e, const Formula& guard);
  Expression VisitAddition(const Expression& e, const Formula& guard);
  Expression VisitMultiplication(const Expression& e, const Formula& guard);
  Expression VisitDivision(const Expression& e, const Formula& guard);
  Expression VisitLog(const Expression& e, const Formula& guard);
  Expression VisitAbs(const Expression& e, const Formula& guard);
  Expression VisitExp(const Expression& e, const Formula& guard);
  Expression VisitSqrt(const Expression& e, const Formula& guard);
  Expression VisitPow(const Expression& e, const Formula& guard);
  Expression VisitSin(const Expression& e, const Formula& guard);
  Expression VisitCos(const Expression& e, const Formula& guard);
  Expression VisitTan(const Expression& e, const Formula& guard);
  Expression VisitAsin(const Expression& e, const Formula& guard);
  Expression VisitAcos(const Expression& e, const Formula& guard);
  Expression VisitAtan(const Expression& e, const Formula& guard);
  Expression VisitAtan2(const Expression& e, const Formula& guard);
  Expression VisitSinh(const Expression& e, const Formula& guard);
  Expression VisitCosh(const Expression& e, const Formula& guard);
  Expression VisitTanh(const Expression& e, const Formula& guard);
  Expression VisitMin(const Expression& e, const Formula& guard);
  Expression VisitMax(const Expression& e, const Formula& guard);
  Expression VisitIfThenElse(const Expression& e, const Formula& guard);
  Expression VisitUninterpretedFunction(const Expression& e,
                                        const Formula& guard);

  // Handle formula
  Formula Visit(const Formula& f, const Formula& guard);
  Formula VisitFalse(const Formula& f, const Formula& guard);
  Formula VisitTrue(const Formula& f, const Formula& guard);
  Formula VisitVariable(const Formula& f, const Formula& guard);
  Formula VisitEqualTo(const Formula& f, const Formula& guard);
  Formula VisitNotEqualTo(const Formula& f, const Formula& guard);
  Formula VisitGreaterThan(const Formula& f, const Formula& guard);
  Formula VisitGreaterThanOrEqualTo(const Formula& f, const Formula& guard);
  Formula VisitLessThan(const Formula& f, const Formula& guard);
  Formula VisitLessThanOrEqualTo(const Formula& f, const Formula& guard);
  Formula VisitConjunction(const Formula& f, const Formula& guard);
  Formula VisitDisjunction(const Formula& f, const Formula& guard);
  Formula VisitNegation(const Formula& f, const Formula& guard);
  Formula VisitForall(const Formula& f, const Formula& guard);

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
                                                        const Formula&,
                                                        const Formula&);
  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend Expression drake::symbolic::VisitExpression<Expression>(
      IfThenElseEliminator*, const Expression&, const Formula&);
};
}  // namespace dreal
