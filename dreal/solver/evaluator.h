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

/// Represents the evaluation result of a constraint given a box.
class EvaluationResult {
 public:
  enum class Type {
    VALID,    ///< Any point in the box satisfies the constraint.
    UNSAT,    ///< There is no point in the box satisfying the constraint.
    UNKNOWN,  ///< It is unknown. It may indicate that there is a
              /// point in the box satisfying the constraint.
  };

  /// Constructs an EvaluationResult with @p type and @p evaluation.
  EvaluationResult(Type type, Box::Interval evaluation);

  /// Returns the type of this result.
  Type type() const;

  /// Returns the interval evaluation of this result.
  const Box::Interval& evaluation() const;

 private:
  Type type_;

  // Given e₁ rop e₂, it keeps the result of the interval evaluation of (e₁ -
  // e₂) over a box.
  Box::Interval evaluation_;
};

/// Class to evaluate a symbolic formula with a box.
class Evaluator {
 public:
  // No default constructor.
  Evaluator() = delete;

  /// Default copy constructor.
  Evaluator(const Evaluator&) = default;

  /// Default move constructor.
  Evaluator(Evaluator&&) = default;

  /// Default copy assign operator.
  Evaluator& operator=(const Evaluator&) = default;

  /// Default move assign operator.
  Evaluator& operator=(Evaluator&&) = default;

  /// Evaluates the constraint/formula with @p box.
  EvaluationResult operator()(const Box& box) const;

 private:
  // Constructs an Evaluator from `ptr`.
  explicit Evaluator(std::shared_ptr<EvaluatorCell> ptr);

  std::shared_ptr<EvaluatorCell> ptr_;

  friend std::ostream& operator<<(std::ostream& os, const Evaluator& evaluator);

  friend Evaluator make_evaluator_quantifier_free(
      const Formula& f, const std::vector<Variable>& variables);

  friend Evaluator make_evaluator_forall(const Formula& f,
                                         const std::vector<Variable>& variables,
                                         double epsilon, double delta);
};

Evaluator make_evaluator_quantifier_free(
    const Formula& f, const std::vector<Variable>& variables);

Evaluator make_evaluator_forall(const Formula& f,
                                const std::vector<Variable>& variable,
                                double epsilon, double delta);

std::ostream& operator<<(std::ostream& os, const Evaluator& evaluator);

}  // namespace dreal
