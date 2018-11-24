#pragma once

#include <ostream>

#include "./ibex.h"

#include "dreal/solver/expression_evaluator.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/solver/formula_evaluator_cell.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

/// Evaluator for relational formulas.
class RelationalFormulaEvaluator : public FormulaEvaluatorCell {
 public:
  explicit RelationalFormulaEvaluator(Formula f);

  /// Deleted copy-constructor.
  RelationalFormulaEvaluator(const RelationalFormulaEvaluator&) = delete;

  /// Deleted move-constructor.
  RelationalFormulaEvaluator(RelationalFormulaEvaluator&&) = default;

  /// Deleted copy-assignment operator.
  RelationalFormulaEvaluator& operator=(const RelationalFormulaEvaluator&) =
      delete;

  /// Deleted move-assignment operator.
  RelationalFormulaEvaluator& operator=(RelationalFormulaEvaluator&&) = delete;

  ~RelationalFormulaEvaluator() override;

  FormulaEvaluationResult operator()(const Box& box) const override;

  std::ostream& Display(std::ostream& os) const override;

  const Variables& variables() const override {
    return expression_evaluator_.variables();
  }

 private:
  const RelationalOperator op_{};
  const ExpressionEvaluator expression_evaluator_;
};
}  // namespace dreal
