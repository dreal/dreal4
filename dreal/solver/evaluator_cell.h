#pragma once

#include <memory>
#include <vector>

#include "dreal/solver/context.h"
#include "dreal/solver/evaluator.h"
#include "dreal/util/box.h"
#include "dreal/util/ibex_converter.h"

namespace dreal {

/// Base type for evaluator cell types.
class EvaluatorCell {
 public:
  virtual ~EvaluatorCell() = default;

  /// Evaluates the constraint/formula with @p box.
  virtual EvaluationResult operator()(const Box& box) const = 0;

  virtual std::ostream& Display(std::ostream& os) const = 0;
};

/// Evaluator for quantifier-free formulas. It uses IBEX's function
/// evaluation to evaluate QF-formulas.
class EvaluatorQuantifierFree : public EvaluatorCell {
 public:
  ~EvaluatorQuantifierFree() override = default;

  EvaluatorQuantifierFree(const Formula& f,
                          const std::vector<Variable>& variables);

  EvaluationResult operator()(const Box& box) const override;

  std::ostream& Display(std::ostream& os) const override;

 private:
  const std::shared_ptr<IbexConverter> ibex_converter_;
  RelationalOperator op_{};
  std::shared_ptr<ibex::Function> func_;
};

/// Evaluator for forall formulas.
class EvaluatorForall : public EvaluatorCell {
 public:
  ~EvaluatorForall() override = default;

  EvaluatorForall(const Formula& f, const std::vector<Variable>& variables,
                  double delta);

  EvaluationResult operator()(const Box& box) const override;

  std::ostream& Display(std::ostream& os) const override;

 private:
  const Formula f_;
  mutable Context context_;
  const double delta_;
};
}  // namespace dreal
