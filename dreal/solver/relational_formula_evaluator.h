#pragma once

#include <memory>
#include <ostream>
#include <vector>

#include "./ibex.h"

#include "dreal/solver/expression_evaluator.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/solver/formula_evaluator_cell.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/ibex_converter.h"

namespace dreal {

/// Evaluator for relational formulas. It uses IBEX's function
/// evaluation to evaluate them.
class RelationalFormulaEvaluator : public FormulaEvaluatorCell {
 public:
  RelationalFormulaEvaluator(RelationalOperator op,
                             ExpressionEvaluator expression_evaluator);

  /// Creates a RelationalFormulaEvaluator from @p f and @p variables.
  static RelationalFormulaEvaluator Make(
      const Formula& f, const std::vector<Variable>& variables);

  ~RelationalFormulaEvaluator() override;

  FormulaEvaluationResult operator()(const Box& box) const override;

  std::ostream& Display(std::ostream& os) const override;

 private:
  const RelationalOperator op_{};
  const ExpressionEvaluator expression_evaluator_;
};
}  // namespace dreal
