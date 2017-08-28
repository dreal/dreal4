#pragma once

#include <memory>
#include <ostream>
#include <vector>

#include "./ibex.h"

#include "dreal/util/box.h"
#include "dreal/util/ibex_converter.h"
#include "dreal/util/logging.h"
#include "dreal/util/symbolic.h"

namespace dreal {

/// Class to evaluate a symbolic formula with a box.
class Evaluator {
 public:
  /// Constructs an Evaluator using @p.
  Evaluator(const Formula& f, const std::vector<Variable>& variables);

  /// Evaluates the constraint/formula with @p box.
  Box::Interval Eval(const Box& box) const;

 private:
  std::shared_ptr<IbexConverter> ibex_converter_;
  std::shared_ptr<const ibex::ExprCtr> expr_ctr_;
  std::shared_ptr<ibex::Function> func_;

  friend std::ostream& operator<<(std::ostream& os, const Evaluator& evaluator);
};

std::ostream& operator<<(std::ostream& os, const Evaluator& evaluator);

}  // namespace dreal
