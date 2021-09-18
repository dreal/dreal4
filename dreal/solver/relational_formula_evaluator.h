/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
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
