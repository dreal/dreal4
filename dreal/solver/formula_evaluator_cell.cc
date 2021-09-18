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
#include "dreal/solver/formula_evaluator_cell.h"

#include <utility>

namespace dreal {

namespace {
bool is_simple_relational(const Formula& f) {
  if (is_negation(f)) {
    return is_simple_relational(get_operand(f));
  }
  if (!is_relational(f)) {
    return false;
  }
  const Expression& lhs{get_lhs_expression(f)};
  const Expression& rhs{get_rhs_expression(f)};
  return ((is_constant(lhs) || is_real_constant(lhs)) && is_variable(rhs)) ||
         (is_variable(lhs) && (is_constant(rhs) || is_real_constant(rhs)));
}

bool is_neq(const Formula& f, const bool polarity = true) {
  if (is_negation(f)) {
    return is_neq(get_operand(f), !polarity);
  }
  if (!is_relational(f)) {
    return false;
  }
  return (polarity && is_not_equal_to(f)) || (!polarity && is_equal_to(f));
}

}  // namespace

FormulaEvaluatorCell::FormulaEvaluatorCell(Formula f)
    : f_{std::move(f)},
      is_simple_relational_{dreal::is_simple_relational(f_)},
      is_neq_{dreal::is_neq(f_, true)} {}

}  // namespace dreal
