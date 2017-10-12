#pragma once

#include <memory>
#include <ostream>
#include <vector>

#include "./ibex.h"

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
  RelationalFormulaEvaluator(const Formula& f,
                             const std::vector<Variable>& variables);

  ~RelationalFormulaEvaluator() override;

  FormulaEvaluationResult operator()(const Box& box) const override;

  std::ostream& Display(std::ostream& os) const override;

 private:
  const std::shared_ptr<IbexConverter> ibex_converter_;
  RelationalOperator op_{};
  std::shared_ptr<ibex::Function> func_;
};
}  // namespace dreal
