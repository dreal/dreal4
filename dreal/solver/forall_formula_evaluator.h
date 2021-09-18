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

#include <memory>
#include <ostream>
#include <vector>

#include "dreal/solver/context.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/solver/formula_evaluator_cell.h"
#include "dreal/solver/relational_formula_evaluator.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

/// Evaluator for forall formulas.
///
/// In the standard first-order logic semantics, A universally
/// quantified formula is evaluated to a Boolean value. Here, however,
/// we want to have a quantitative measure when a
/// universally-quantified formula is false. We return an error
/// interval in order to utilize it as a termination criteria in ICP
/// (Interval Constraint Propagation).
///
/// Given `f = ∀y. [(e₁(x, y) ≥ 0) ∨ ... ∨ (eₙ(x, y) ≥ 0)]`, we check
/// if there is a counterexample of f. To prevent a spurious
/// counterexample, we check the satisfiability of the ε-strengthened
/// version of the negation of the nested formula, `strengthen((e₁(x,
/// y) < 0) ∧ ... ∧ (eₙ(x, y) < 0), ε)`, with delta = δ. There can be
/// two possible results for this query:
///
///  - UNSAT: Return a zero error-interval, `[0, 0]`.
///
///  - δ-SAT: Given a counter example `(a, b)`, evaluate `eᵢ(Iₓ, b)`
///           where `Iₓ` is the current interval assignment on x.
///           Returns `[0, maxᵢ{|eᵢ(Iₓ, b)|}]`.
///
class ForallFormulaEvaluator : public FormulaEvaluatorCell {
 public:
  // To use this class in multi multiple threads, it is required to provide the
  // number of jobs.
  ForallFormulaEvaluator(Formula f, double epsilon, double delta,
                         int number_of_jobs);

  /// Deleted copy constructor.
  ForallFormulaEvaluator(const ForallFormulaEvaluator&) = delete;

  /// Deleted move constructor.
  ForallFormulaEvaluator(ForallFormulaEvaluator&&) = delete;

  /// Deleted copy-assignment operator.
  ForallFormulaEvaluator& operator=(const ForallFormulaEvaluator&) = delete;

  /// Deleted move-assignment operator.
  ForallFormulaEvaluator& operator=(ForallFormulaEvaluator&&) = delete;

  /// Default destructor.
  ~ForallFormulaEvaluator() override = default;

  FormulaEvaluationResult operator()(const Box& box) const override;

  std::ostream& Display(std::ostream& os) const override;

  const Variables& variables() const override;

 private:
  Context& GetContext() const;

  std::vector<RelationalFormulaEvaluator> evaluators_;

  // To make this class thread-safe, it includes a vector of Contexts and each
  // thread owns a unique Context instance.
  mutable std::vector<Context> contexts_;
};

}  // namespace dreal
