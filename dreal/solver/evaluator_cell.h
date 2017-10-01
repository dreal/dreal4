#pragma once

#include <memory>
#include <ostream>
#include <vector>

#include "dreal/solver/evaluator.h"
#include "dreal/util/box.h"

namespace dreal {

/// Base type for evaluator cell types.
class EvaluatorCell {
 public:
  virtual ~EvaluatorCell() = default;

  /// Evaluates the constraint/formula with @p box.
  virtual EvaluationResult operator()(const Box& box) const = 0;

  virtual std::ostream& Display(std::ostream& os) const = 0;
};

}  // namespace dreal
