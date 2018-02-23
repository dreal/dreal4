#pragma once

#include <iostream>

#include "dreal/symbolic/symbolic.h"

/// Sum type of symbolic::Expression and symbolic::Formula.
namespace dreal {
class Term {
 public:
  enum class Type { EXPRESSION, FORMULA };

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

 private:
  Type type_;
  Expression e_;
  Formula f_;
};

std::ostream& operator<<(std::ostream& os, const Term& t);
}  // namespace dreal
