#pragma once

#include <ostream>

#include "./ibex.h"

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

class ExpressionEvaluator {
 public:
  explicit ExpressionEvaluator(Expression e);

  /// Evaluates the expression with @p box.
  Box::Interval operator()(const Box& box) const;

  const Variables& variables() const { return e_.GetVariables(); }

 private:
  Box::Interval Visit(const Expression& e, const Box& box) const;
  Box::Interval VisitVariable(const Expression& e, const Box& box) const;
  Box::Interval VisitConstant(const Expression& e, const Box& box) const;
  Box::Interval VisitRealConstant(const Expression& e, const Box& box) const;
  Box::Interval VisitAddition(const Expression& e, const Box& box) const;
  Box::Interval VisitMultiplication(const Expression& e, const Box& box) const;
  Box::Interval VisitDivision(const Expression& e, const Box& box) const;
  Box::Interval VisitLog(const Expression& e, const Box& box) const;
  Box::Interval VisitAbs(const Expression& e, const Box& box) const;
  Box::Interval VisitExp(const Expression& e, const Box& box) const;
  Box::Interval VisitSqrt(const Expression& e, const Box& box) const;
  Box::Interval VisitPow(const Expression& e, const Box& box) const;

  // Evaluates `pow(e1, e2)` with the @p box.
  Box::Interval VisitPow(const Expression& e1, const Expression& e2,
                         const Box& box) const;
  Box::Interval VisitSin(const Expression& e, const Box& box) const;
  Box::Interval VisitCos(const Expression& e, const Box& box) const;
  Box::Interval VisitTan(const Expression& e, const Box& box) const;
  Box::Interval VisitAsin(const Expression& e, const Box& box) const;
  Box::Interval VisitAcos(const Expression& e, const Box& box) const;
  Box::Interval VisitAtan(const Expression& e, const Box& box) const;
  Box::Interval VisitAtan2(const Expression& e, const Box& box) const;
  Box::Interval VisitSinh(const Expression& e, const Box& box) const;
  Box::Interval VisitCosh(const Expression& e, const Box& box) const;
  Box::Interval VisitTanh(const Expression& e, const Box& box) const;
  Box::Interval VisitMin(const Expression& e, const Box& box) const;
  Box::Interval VisitMax(const Expression& e, const Box& box) const;
  Box::Interval VisitIfThenElse(const Expression& e, const Box& box) const;
  Box::Interval VisitUninterpretedFunction(const Expression& e,
                                           const Box& box) const;

  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend Box::Interval drake::symbolic::VisitExpression<Box::Interval>(
      const ExpressionEvaluator*, const Expression&, const Box&);

  friend std::ostream& operator<<(
      std::ostream& os, const ExpressionEvaluator& expression_evaluator);

  const Expression e_;
};

std::ostream& operator<<(std::ostream& os,
                         const ExpressionEvaluator& expression_evaluator);

}  // namespace dreal
