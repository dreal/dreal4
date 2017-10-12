#pragma once

#include <memory>
#include <ostream>
#include <vector>

#include "dreal/solver/formula_evaluator.h"
#include "dreal/util/box.h"

namespace dreal {

/// Base type for evaluator cell types.
class FormulaEvaluatorCell {
 public:
  virtual ~FormulaEvaluatorCell() = default;

  /// Evaluates the constraint/formula with @p box.
  virtual FormulaEvaluationResult operator()(const Box& box) const = 0;

  virtual std::ostream& Display(std::ostream& os) const = 0;
};

}  // namespace dreal
