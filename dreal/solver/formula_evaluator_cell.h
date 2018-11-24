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
  explicit FormulaEvaluatorCell(Formula f);

  /// Deleted copy-constructor.
  FormulaEvaluatorCell(const FormulaEvaluatorCell&) = delete;

  /// Deleted move-constructor.
  FormulaEvaluatorCell(FormulaEvaluatorCell&&) = default;

  /// Deleted copy-assignment operator.
  FormulaEvaluatorCell& operator=(const FormulaEvaluatorCell&) = delete;

  /// Deleted move-assignment operator.
  FormulaEvaluatorCell& operator=(FormulaEvaluatorCell&&) = delete;

  /// Default destructor.
  virtual ~FormulaEvaluatorCell() = default;

  const Formula& formula() const { return f_; }

  /// Evaluates the constraint/formula with @p box.
  virtual FormulaEvaluationResult operator()(const Box& box) const = 0;

  virtual const Variables& variables() const = 0;

  virtual std::ostream& Display(std::ostream& os) const = 0;

 private:
  const Formula f_;
};

}  // namespace dreal
