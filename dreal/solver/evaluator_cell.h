#pragma once

#include <memory>
#include <vector>

#include "dreal/solver/context.h"
#include "dreal/util/box.h"
#include "dreal/util/ibex_converter.h"

namespace dreal {

/// Base type for evaluator cell types.
class EvaluatorCell {
 public:
  virtual ~EvaluatorCell() = default;

  /// Evaluates the constraint/formula with @p box.
  virtual Box::Interval operator()(const Box& box) const = 0;

  virtual std::ostream& Display(std::ostream& os) const = 0;
};

/// Evaluator for quantifier-free formulas. It uses IBEX's function
/// evaluation to evaluate QF-formulas.
class EvaluatorQuantifierFree : public EvaluatorCell {
 public:
  ~EvaluatorQuantifierFree() override = default;

  EvaluatorQuantifierFree(const Formula& f,
                          const std::vector<Variable>& variables);

  Box::Interval operator()(const Box& box) const override;

  std::ostream& Display(std::ostream& os) const override;

 private:
  std::shared_ptr<IbexConverter> ibex_converter_;
  std::shared_ptr<const ibex::ExprCtr> expr_ctr_;
  std::shared_ptr<ibex::Function> func_;
};

/// Evaluator for forall formulas.
class EvaluatorForall : public EvaluatorCell {
 public:
  ~EvaluatorForall() override = default;

  EvaluatorForall(const Formula& f, const std::vector<Variable>& variables,
                  double delta);

  Box::Interval operator()(const Box& box) const override;

  std::ostream& Display(std::ostream& os) const override;

 private:
  const Formula f_;
  mutable Context context_;
  const double delta_;
};
}  // namespace dreal
