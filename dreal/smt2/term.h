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

#include <iostream>

#include "dreal/smt2/sort.h"
#include "dreal/symbolic/symbolic.h"

/// Sum type of symbolic::Expression and symbolic::Formula.
namespace dreal {
class Term {
 public:
  enum class Type { EXPRESSION, FORMULA };

  /// Default Constructor. It constructs Term(false).
  Term();

  /// Construct a term with @p e.
  explicit Term(Expression e);

  /// Construct a term with @p f.
  explicit Term(Formula f);

  /// Default copy constructor.
  Term(const Term&) = default;

  /// Default move constructor.
  Term(Term&&) = default;

  /// Default copy assign operator.
  Term& operator=(const Term&) = default;

  /// Default move assign operator.
  Term& operator=(Term&&) = default;

  /// Default destructor.
  ~Term() = default;

  /// Assignment operator.
  Term& operator=(Expression e);

  /// Assignment operator.
  Term& operator=(Formula f);

  /// Returns its type.
  Type type() const;

  /// Returns the expression inside.
  /// @throw runtime_error if it does not include an expression.
  const Expression& expression() const;

  /// Returns the expression inside.
  /// @throw runtime_error if it does not include an expression.
  Expression& mutable_expression();

  /// Returns the formula inside.
  /// @throw runtime_error if it does not include a formula.
  const Formula& formula() const;

  /// Returns the formula inside.
  /// @throw runtime_error if it does not include a formula.
  Formula& mutable_formula();

  /// Creates a new term which substitutes the variable `v` in this term with
  /// `t`.
  Term Substitute(const Variable& v, const Term& t);

  /// Checks if this term can be matched with `s`. Throws std::runtime_error if
  /// `s` is mismatched.
  void Check(Sort s) const;

  /// Checks if this term can be matched with `t`. Throws std::runtime_error if
  /// `t` is mismatched.
  void Check(Variable::Type t) const;

 private:
  Type type_;
  Expression e_;
  Formula f_;
};

std::ostream& operator<<(std::ostream& os, const Term& t);
}  // namespace dreal
