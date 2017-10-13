#pragma once

#include <memory>
#include <ostream>
#include <vector>

#include "./ibex.h"

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/ibex_converter.h"

namespace dreal {
class ExpressionEvaluator {
 public:
  // No default constructor.
  ExpressionEvaluator() = delete;

  // Constructs from @p e using @p variables.
  ExpressionEvaluator(const Expression& e,
                      const std::vector<Variable>& variables);

  // Constructs from @p e using @p box.
  ExpressionEvaluator(const Expression& e, const Box& box);

  /// Default copy constructor.
  ExpressionEvaluator(const ExpressionEvaluator&) = default;

  /// Default move constructor.
  ExpressionEvaluator(ExpressionEvaluator&&) = default;

  /// Default copy assign operator.
  ExpressionEvaluator& operator=(const ExpressionEvaluator&) = default;

  /// Default move assign operator.
  ExpressionEvaluator& operator=(ExpressionEvaluator&&) = default;

  /// Evaluates the expression with @p box.
  Box::Interval operator()(const Box& box) const;

  /// Evaluates the expression at the center of a given @p box.
  /// @note It returns a double, not an interval.
  double EvaluateAtCenter(const Box& box) const;

  // We allows the following friends who need to access func_ member.
  friend class RelationalFormulaEvaluator;
  friend std::ostream& operator<<(
      std::ostream& os, const ExpressionEvaluator& expression_evaluator);

 private:
  const std::shared_ptr<IbexConverter> ibex_converter_;
  std::shared_ptr<ibex::Function> func_;
};

std::ostream& operator<<(std::ostream& os,
                         const ExpressionEvaluator& expression_evaluator);

}  // namespace dreal
