#pragma once

#include <memory>
#include <ostream>
#include <vector>

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/logging.h"

namespace dreal {

// Forward declaration.
class EvaluatorCell;

/// Class to evaluate a symbolic formula with a box.
class Evaluator {
 public:
  // No default constructor.
  Evaluator() = delete;

  Evaluator(const Formula& f, const std::vector<Variable>& variables,
            double delta);

  /// Default copy constructor.
  Evaluator(const Evaluator&) = default;

  /// Default move constructor.
  Evaluator(Evaluator&&) = default;

  /// Default copy assign operator.
  Evaluator& operator=(const Evaluator&) = default;

  /// Default move assign operator.
  Evaluator& operator=(Evaluator&&) = default;

  /// Evaluates the constraint/formula with @p box.
  Box::Interval operator()(const Box& box) const;

 private:
  std::shared_ptr<EvaluatorCell> ptr_;

  friend std::ostream& operator<<(std::ostream& os, const Evaluator& evaluator);

  friend Evaluator make_evaluator_quantifier_free(
      const Formula& f, const std::vector<Variable>& variables);

  friend Evaluator make_evaluator_forall(
      const Formula& f, const std::vector<Variable>& variables);
};

std::ostream& operator<<(std::ostream& os, const Evaluator& evaluator);

}  // namespace dreal
