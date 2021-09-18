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
#include "dreal/solver/formula_evaluator.h"

#include <cassert>
#include <utility>

#include "dreal/solver/expression_evaluator.h"
#include "dreal/solver/forall_formula_evaluator.h"
#include "dreal/solver/formula_evaluator_cell.h"
#include "dreal/solver/relational_formula_evaluator.h"
#include "dreal/util/assert.h"
#include "dreal/util/exception.h"

namespace dreal {

using std::make_shared;
using std::ostream;
using std::shared_ptr;

FormulaEvaluationResult::FormulaEvaluationResult(
    Type type, const Box::Interval& evaluation)
    : type_{type}, evaluation_{evaluation} {}

FormulaEvaluationResult::Type FormulaEvaluationResult::type() const {
  return type_;
}

const Box::Interval& FormulaEvaluationResult::evaluation() const {
  return evaluation_;
}

ostream& operator<<(ostream& os, FormulaEvaluationResult::Type type) {
  switch (type) {
    case FormulaEvaluationResult::Type::VALID:
      return os << "VALID";
    case FormulaEvaluationResult::Type::UNSAT:
      return os << "UNSAT";
    case FormulaEvaluationResult::Type::UNKNOWN:
      return os << "UNKNOWN";
  }
  DREAL_UNREACHABLE();
}

ostream& operator<<(ostream& os, const FormulaEvaluationResult& result) {
  return os << "[" << result.type() << ", " << result.evaluation() << "]";
}

FormulaEvaluator::FormulaEvaluator(std::shared_ptr<FormulaEvaluatorCell> ptr)
    : ptr_{std::move(ptr)} {
  DREAL_ASSERT(ptr_);
}

FormulaEvaluationResult FormulaEvaluator::operator()(const Box& box) const {
  return (*ptr_)(box);
}

const Variables& FormulaEvaluator::variables() const {
  return ptr_->variables();
}

const Formula& FormulaEvaluator::formula() const { return ptr_->formula(); }

bool FormulaEvaluator::is_simple_relational() const {
  return ptr_->is_simple_relational();
}

bool FormulaEvaluator::is_neq() const { return ptr_->is_neq(); }

ostream& operator<<(ostream& os, const FormulaEvaluator& evaluator) {
  return evaluator.ptr_->Display(os);
}

FormulaEvaluator make_relational_formula_evaluator(const Formula& f) {
  return FormulaEvaluator{make_shared<RelationalFormulaEvaluator>(f)};
}

FormulaEvaluator make_forall_formula_evaluator(const Formula& f,
                                               const double epsilon,
                                               const double delta,
                                               int number_of_jobs) {
  DREAL_ASSERT(is_forall(f));
  return FormulaEvaluator{
      make_shared<ForallFormulaEvaluator>(f, epsilon, delta, number_of_jobs)};
}

}  // namespace dreal
