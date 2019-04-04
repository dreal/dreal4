#pragma once

#include <algorithm>  // for cpplint only
#include <cstddef>
#include <functional>
#include <limits>
#include <map>
#include <ostream>
#include <string>
#include <type_traits>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dreal/symbolic/hash.h"
#include "dreal/symbolic/symbolic_environment.h"
#include "dreal/symbolic/symbolic_variable.h"
#include "dreal/symbolic/symbolic_variables.h"

namespace dreal {
namespace drake {
namespace symbolic {

/** Kinds of symbolic expressions. */
enum class ExpressionKind {
  Constant,               ///< floating-point constant (double)
  RealConstant,           ///< real constant (represented by an interval)
  Var,                    ///< variable
  Add,                    ///< addition (+)
  Mul,                    ///< multiplication (*)
  Div,                    ///< division (/)
  Log,                    ///< logarithms
  Abs,                    ///< absolute value function
  Exp,                    ///< exponentiation
  Sqrt,                   ///< square root
  Pow,                    ///< power function
  Sin,                    ///< sine
  Cos,                    ///< cosine
  Tan,                    ///< tangent
  Asin,                   ///< arcsine
  Acos,                   ///< arccosine
  Atan,                   ///< arctangent
  Atan2,                  ///< arctangent2 (atan2(y,x) = atan(y/x))
  Sinh,                   ///< hyperbolic sine
  Cosh,                   ///< hyperbolic cosine
  Tanh,                   ///< hyperbolic tangent
  Min,                    ///< min
  Max,                    ///< max
  IfThenElse,             ///< if then else
  NaN,                    ///< NaN
  UninterpretedFunction,  ///< Uninterpreted function
  // TODO(soonho): add Integral
};

/** Total ordering between ExpressionKinds. */
bool operator<(ExpressionKind k1, ExpressionKind k2);

class ExpressionCell;                   // In symbolic_expression_cell.h
class ExpressionConstant;               // In symbolic_expression_cell.h
class ExpressionRealConstant;           // In symbolic_expression_cell.h
class ExpressionVar;                    // In symbolic_expression_cell.h
class UnaryExpressionCell;              // In symbolic_expression_cell.h
class BinaryExpressionCell;             // In symbolic_expression_cell.h
class ExpressionAdd;                    // In symbolic_expression_cell.h
class ExpressionMul;                    // In symbolic_expression_cell.h
class ExpressionDiv;                    // In symbolic_expression_cell.h
class ExpressionLog;                    // In symbolic_expression_cell.h
class ExpressionAbs;                    // In symbolic_expression_cell.h
class ExpressionExp;                    // In symbolic_expression_cell.h
class ExpressionSqrt;                   // In symbolic_expression_cell.h
class ExpressionPow;                    // In symbolic_expression_cell.h
class ExpressionSin;                    // In symbolic_expression_cell.h
class ExpressionCos;                    // In symbolic_expression_cell.h
class ExpressionTan;                    // In symbolic_expression_cell.h
class ExpressionAsin;                   // In symbolic_expression_cell.h
class ExpressionAcos;                   // In symbolic_expression_cell.h
class ExpressionAtan;                   // In symbolic_expression_cell.h
class ExpressionAtan2;                  // In symbolic_expression_cell.h
class ExpressionSinh;                   // In symbolic_expression_cell.h
class ExpressionCosh;                   // In symbolic_expression_cell.h
class ExpressionTanh;                   // In symbolic_expression_cell.h
class ExpressionMin;                    // In symbolic_expression_cell.h
class ExpressionMax;                    // In symbolic_expression_cell.h
class ExpressionIfThenElse;             // In symbolic_expression_cell.h
class ExpressionUninterpretedFunction;  // In symbolic_expression_cell.h
class Formula;                          // In symbolic_formula.h
class Expression;

// ExpressionSubstitution is a map from a Variable to a symbolic expression. It
// is used in Expression::Substitute and Formula::Substitute methods as an
// argument.
using ExpressionSubstitution =
    std::unordered_map<Variable, Expression, hash_value<Variable>>;

// FormulaSubstitution is a map from a Variable to a symbolic formula. It
// is used in Expression::Substitute and Formula::Substitute methods as an
// argument.
using FormulaSubstitution =
    std::unordered_map<Variable, Formula, hash_value<Variable>>;

/** Represents a symbolic form of an expression.

Its syntax tree is as follows:

@verbatim
    E := Var | Constant(double) | RealConstant(double, double)
       | E + ... + E | E * ... * E | E / E | log(E)
       | abs(E) | exp(E) | sqrt(E) | pow(E, E) | sin(E) | cos(E) | tan(E)
       | asin(E) | acos(E) | atan(E) | atan2(E, E) | sinh(E) | cosh(E) | tanh(E)
       | min(E, E) | max(E, E) | if_then_else(F, E, E) | NaN
       | uninterpreted_function(name, {v_1, ..., v_n})
@endverbatim

In the implementation, Expression is a simple wrapper including a
pointer to ExpressionCell class which is a super-class of different
kinds of symbolic expressions (i.e. ExpressionAdd, ExpressionMul,
ExpressionLog, ExpressionSin).

@note The sharing of sub-expressions is not yet implemented.

@note -E is represented as -1 * E internally.

@note A subtraction E1 - E2 is represented as E1 + (-1 * E2) internally.

The following simple simplifications are implemented:
@verbatim
    E + 0             ->  E
    0 + E             ->  E
    E - 0             ->  E
    E - E             ->  0
    E * 1             ->  E
    1 * E             ->  E
    E * 0             ->  0
    0 * E             ->  0
    E / 1             ->  E
    E / E             ->  1
    pow(E, 0)         ->  1
    pow(E, 1)         ->  E
    E * E             ->  E^2 (= pow(E, 2))
    sqrt(E * E)       ->  |E| (= abs(E))
    sqrt(E) * sqrt(E) -> E
@endverbatim

Constant folding is implemented:
@verbatim
    E(c1) + E(c2)  ->  E(c1 + c2)    // c1, c2 are constants
    E(c1) - E(c2)  ->  E(c1 - c2)
    E(c1) * E(c2)  ->  E(c1 * c2)
    E(c1) / E(c2)  ->  E(c1 / c2)
    f(E(c))        ->  E(f(c))       // c is a constant, f is a math function
@endverbatim

For the math functions which are only defined over a restricted domain (namely,
log, sqrt, pow, asin, acos), we check the domain of argument(s), and throw
std::domain_error exception if a function is not well-defined for a given
argument(s).

Relational operators over expressions (==, !=, <, >, <=, >=) return
symbolic::Formula instead of bool. Those operations are declared in
symbolic_formula.h file. To check structural equality between two expressions a
separate function, Expression::EqualTo, is provided.

*/
class Expression {
 public:
  Expression(const Expression&);
  Expression& operator=(const Expression&);
  Expression(Expression&&) noexcept;
  Expression& operator=(Expression&&) noexcept;
  ~Expression();

  /** Default constructor. It constructs Zero(). */
  Expression();

  /** Constructs a constant (floating-point). */
  // NOLINTNEXTLINE(runtime/explicit): This conversion is desirable.
  Expression(double d);
  /** Constructs an expression from @p var.
   * @pre @p var is neither a dummy nor a BOOLEAN variable.
   */
  // NOLINTNEXTLINE(runtime/explicit): This conversion is desirable.
  Expression(const Variable& var);
  /** Returns expression kind. */
  ExpressionKind get_kind() const;
  /** Returns hash value. */
  size_t get_hash() const;
  /** Collects variables in expression.
   *
   * @note For the first call, it traverses every node in the
   * expression tree and caches the result. The following calls are
   * done in O(1) time.
   */
  const Variables& GetVariables() const;

  /** Checks structural equality.
   *
   * Two expressions e1 and e2 are structurally equal when they have the same
   * internal AST(abstract-syntax tree) representation. Please note that we can
   * have two computationally (or extensionally) equivalent expressions which
   * are not structurally equal. For example, consider:
   *
   *    e1 = 2 * (x + y)
   *    e2 = 2x + 2y
   *
   * Obviously, we know that e1 and e2 are evaluated to the same value for all
   * assignments to x and y. However, e1 and e2 are not structurally equal by
   * the definition. Note that e1 is a multiplication expression
   * (is_multiplication(e1) is true) while e2 is an addition expression
   * (is_addition(e2) is true).
   *
   * One main reason we use structural equality in EqualTo is due to
   * Richardson's Theorem. It states that checking ∀x. E(x) = F(x) is
   * undecidable when we allow sin, asin, log, exp in E and F. Read
   * https://en.wikipedia.org/wiki/Richardson%27s_theorem for details.
   *
   * Note that for polynomial cases, you can use Expand method and check if two
   * polynomial expressions p1 and p2 are computationally equal. To do so, you
   * check the following:
   *
   *     (p1.Expand() - p2.Expand()).EqualTo(0).
   */
  bool EqualTo(const Expression& e) const;

  /** Provides lexicographical ordering between expressions.
      This function is used as a compare function in map<Expression> and
      set<Expression> via std::less<dreal::drake::symbolic::Expression>. */
  bool Less(const Expression& e) const;

  /** Checks if this symbolic expression is convertible to Polynomial. */
  bool is_polynomial() const;

  /** Evaluates under a given environment (by default, an empty environment).
   *  @throws std::runtime_error if NaN is detected during evaluation.
   */
  double Evaluate(const Environment& env = Environment{}) const;

  /** Partially evaluates this expression using an environment @p
   * env. Internally, this method promotes @p env into a substitution
   * (Variable → Expression) and call Evaluate::Substitute with it.
   *
   * @throws std::runtime_error if NaN is detected during evaluation.
   */
  Expression EvaluatePartial(const Environment& env) const;

  /** Expands out products and positive integer powers in expression. For
   * example, `(x + 1) * (x - 1)` is expanded to `x^2 - 1` and `(x + y)^2` is
   * expanded to `x^2 + 2xy + y^2`. Note that Expand applies recursively to
   * sub-expressions. For instance, `sin(2 * (x + y))` is expanded to `sin(2x +
   * 2y)`. It also simplifies "division by constant" cases. See
   * "symbolic/test/symbolic_expansion_test.cc" to find the examples.
   *
   * @throws std::runtime_error if NaN is detected during expansion.
   */
  Expression Expand() const;

  /** Returns a copy of this expression replacing all occurrences of @p var
   * with @p e.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Expression Substitute(const Variable& var, const Expression& e) const;

  /** Returns a copy of this expression replacing all occurrences of the
   * variables in @p expr_subst with corresponding expressions in @p expr_subst
   * and all occurrences of the variables in @p formula_subst with corresponding
   * formulas in @p formula_subst.
   *
   * Note that the substitutions occur simultaneously. For example,
   * (x / y).Substitute({{x, y}, {y, x}}, {}) gets (y / x).
   *
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) const;

  /** Returns a copy of this expression replacing all occurrences of the
   * variables in @p expr_subst with corresponding expressions in @p expr_subst.
   *
   * @note This is equivalent to `Substitute(expr_subst, {})`.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Expression Substitute(const ExpressionSubstitution& expr_subst) const;

  /** Returns a copy of this expression replacing all occurrences of the
   * variables in @p formula_subst with corresponding formulas in @p
   * formula_subst.
   *
   * @note This is equivalent to `Substitute({}, formula_subst)`.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Expression Substitute(const FormulaSubstitution& formula_subst) const;

  /** Differentiates this symbolic expression with respect to the variable @p
   * var.
   * @throws std::runtime_error if it is not differentiable.
   */
  Expression Differentiate(const Variable& x) const;

  /** Returns string representation of Expression. */
  std::string to_string() const;

  /** Returns zero. */
  static Expression Zero();
  /** Returns one. */
  static Expression One();
  /** Returns Pi, the ratio of a circle’s circumference to its diameter. */
  static Expression Pi();
  /** Return e, the base of natural logarithms. */
  static Expression E();
  /** Returns NaN (Not-a-Number). */
  static Expression NaN();

  friend Expression operator+(const Expression& lhs, const Expression& rhs);
  friend Expression operator+(const Expression& lhs, Expression&& rhs);
  friend Expression operator+(Expression&& lhs, const Expression& rhs);
  friend Expression operator+(Expression&& lhs, Expression&& rhs);
  // NOLINTNEXTLINE(runtime/references) per C++ standard signature.
  friend Expression& operator+=(Expression& lhs, const Expression& rhs);

  /** Provides prefix increment operator (i.e. ++x). */
  Expression& operator++();
  /** Provides postfix increment operator (i.e. x++). */
  Expression operator++(int);

  friend Expression operator-(const Expression& lhs, const Expression& rhs);
  friend Expression operator-(const Expression& lhs, Expression&& rhs);
  friend Expression operator-(Expression&& lhs, const Expression& rhs);
  friend Expression operator-(Expression&& lhs, Expression&& rhs);
  // NOLINTNEXTLINE(runtime/references) per C++ standard signature.
  friend Expression& operator-=(Expression& lhs, const Expression& rhs);

  /** Provides unary plus operator. */
  friend Expression operator+(const Expression& e);

  /** Provides unary minus operator. */
  friend Expression operator-(const Expression& e);
  friend Expression operator-(Expression&& e);

  /** Provides prefix decrement operator (i.e. --x). */
  Expression& operator--();
  /** Provides postfix decrement operator (i.e. x--). */
  Expression operator--(int);

  friend Expression operator*(const Expression& lhs, const Expression& rhs);
  friend Expression operator*(const Expression& lhs, Expression&& rhs);
  friend Expression operator*(Expression&& lhs, const Expression& rhs);
  friend Expression operator*(Expression&& lhs, Expression&& rhs);
  // NOLINTNEXTLINE(runtime/references) per C++ standard signature.
  friend Expression& operator*=(Expression& lhs, const Expression& rhs);

  friend Expression operator/(Expression lhs, const Expression& rhs);
  // NOLINTNEXTLINE(runtime/references) per C++ standard signature.
  friend Expression& operator/=(Expression& lhs, const Expression& rhs);

  /// Creates an real-constant expression represented by [@p lb, @p
  /// ub]. @p use_lb_as_representative is used to select its
  /// representative value. If it is true, @p lb is used. Otherwise,
  /// @p ub is used.
  friend Expression real_constant(double lb, double ub,
                                  bool use_lb_as_representative);
  friend Expression log(const Expression& e);
  friend Expression abs(const Expression& e);
  friend Expression exp(const Expression& e);
  friend Expression sqrt(const Expression& e);
  friend Expression pow(const Expression& e1, const Expression& e2);
  friend Expression sin(const Expression& e);
  friend Expression cos(const Expression& e);
  friend Expression tan(const Expression& e);
  friend Expression asin(const Expression& e);
  friend Expression acos(const Expression& e);
  friend Expression atan(const Expression& e);
  friend Expression atan2(const Expression& e1, const Expression& e2);
  friend Expression sinh(const Expression& e);
  friend Expression cosh(const Expression& e);
  friend Expression tanh(const Expression& e);
  friend Expression min(const Expression& e1, const Expression& e2);
  friend Expression max(const Expression& e1, const Expression& e2);

  /** Constructs if-then-else expression.

    @verbatim
      if_then_else(cond, expr_then, expr_else)
    @endverbatim

    The value returned by the above if-then-else expression is @p expr_then if
    @p cond is evaluated to true. Otherwise, it returns @p expr_else.

    The semantics is similar to the C++'s conditional expression constructed by
    its ternary operator, @c ?:. However, there is a key difference between the
    C++'s conditional expression and our @c if_then_else expression in a way the
    arguments are evaluated during the construction.

     - In case of the C++'s conditional expression, <tt> cond ? expr_then :
       expr_else</tt>, the then expression @c expr_then (respectively, the else
       expression @c expr_else) is \b only evaluated when the conditional
       expression @c cond is evaluated to \b true (respectively, when @c cond is
       evaluated to \b false).

     - In case of the symbolic expression, <tt>if_then_else(cond, expr_then,
       expr_else)</tt>, however, \b both arguments @c expr_then and @c expr_else
       are evaluated first and then passed to the @c if_then_else function.

     @note This function returns an \b expression and it is different from the
     C++'s if-then-else \b statement.

     @note While it is still possible to define <tt> min, max, abs</tt> math
     functions using @c if_then_else expression, it is highly \b recommended to
     use the provided native definitions for them because it allows solvers to
     detect specific math functions and to have a room for special
     optimizations.

     @note More information about the C++'s conditional expression and ternary
     operator is available at
     http://en.cppreference.com/w/cpp/language/operator_other#Conditional_operator.
   */
  friend Expression if_then_else(const Formula& f_cond,
                                 const Expression& e_then,
                                 const Expression& e_else);
  friend Expression uninterpreted_function(const std::string& name,
                                           const Variables& vars);

  friend std::ostream& operator<<(std::ostream& os, const Expression& e);
  friend void swap(Expression& a, Expression& b) { std::swap(a.ptr_, b.ptr_); }

  friend bool is_constant(const Expression& e);
  friend bool is_real_constant(const Expression& e);
  friend bool is_variable(const Expression& e);
  friend bool is_addition(const Expression& e);
  friend bool is_multiplication(const Expression& e);
  friend bool is_division(const Expression& e);
  friend bool is_log(const Expression& e);
  friend bool is_abs(const Expression& e);
  friend bool is_exp(const Expression& e);
  friend bool is_sqrt(const Expression& e);
  friend bool is_pow(const Expression& e);
  friend bool is_sin(const Expression& e);
  friend bool is_cos(const Expression& e);
  friend bool is_tan(const Expression& e);
  friend bool is_asin(const Expression& e);
  friend bool is_acos(const Expression& e);
  friend bool is_atan(const Expression& e);
  friend bool is_atan2(const Expression& e);
  friend bool is_sinh(const Expression& e);
  friend bool is_cosh(const Expression& e);
  friend bool is_tanh(const Expression& e);
  friend bool is_min(const Expression& e);
  friend bool is_max(const Expression& e);
  friend bool is_if_then_else(const Expression& e);
  friend bool is_uninterpreted_function(const Expression& e);

  // Note that the following cast functions are only for low-level operations
  // and not exposed to the user of symbolic/symbolic_expression.h
  // header. These functions are declared in
  // symbolic/symbolic_expression_cell.h header.
  friend const ExpressionConstant* to_constant(const Expression& e);
  friend const ExpressionRealConstant* to_real_constant(const Expression& e);
  friend const ExpressionVar* to_variable(const Expression& e);
  friend const UnaryExpressionCell* to_unary(const Expression& e);
  friend const BinaryExpressionCell* to_binary(const Expression& e);
  friend const ExpressionAdd* to_addition(const Expression& e);
  friend ExpressionAdd* to_addition(Expression& e);
  friend const ExpressionMul* to_multiplication(const Expression& e);
  friend ExpressionMul* to_multiplication(Expression& e);
  friend const ExpressionDiv* to_division(const Expression& e);
  friend const ExpressionLog* to_log(const Expression& e);
  friend const ExpressionAbs* to_abs(const Expression& e);
  friend const ExpressionExp* to_exp(const Expression& e);
  friend const ExpressionSqrt* to_sqrt(const Expression& e);
  friend const ExpressionPow* to_pow(const Expression& e);
  friend const ExpressionSin* to_sin(const Expression& e);
  friend const ExpressionCos* to_cos(const Expression& e);
  friend const ExpressionTan* to_tan(const Expression& e);
  friend const ExpressionAsin* to_asin(const Expression& e);
  friend const ExpressionAcos* to_acos(const Expression& e);
  friend const ExpressionAtan* to_atan(const Expression& e);
  friend const ExpressionAtan2* to_atan2(const Expression& e);
  friend const ExpressionSinh* to_sinh(const Expression& e);
  friend const ExpressionCosh* to_cosh(const Expression& e);
  friend const ExpressionTanh* to_tanh(const Expression& e);
  friend const ExpressionMin* to_min(const Expression& e);
  friend const ExpressionMax* to_max(const Expression& e);
  friend const ExpressionIfThenElse* to_if_then_else(const Expression& e);
  friend const ExpressionUninterpretedFunction* to_uninterpreted_function(
      const Expression& e);

  friend class ExpressionAddFactory;
  friend class ExpressionMulFactory;
  friend class ExpressionCell;

 private:
  static ExpressionCell* make_cell(double d);

  explicit Expression(ExpressionCell* ptr);

  ExpressionCell* ptr_{nullptr};

  // Storage to cache the result of GetVariables().
  mutable std::shared_ptr<Variables> variables_;
};

Expression operator+(const Expression& lhs, const Expression& rhs);
Expression operator+(const Expression& lhs, Expression&& rhs);
Expression operator+(Expression&& lhs, const Expression& rhs);
Expression operator+(Expression&& lhs, Expression&& rhs);
// NOLINTNEXTLINE(runtime/references) per C++ standard signature.
Expression& operator+=(Expression& lhs, const Expression& rhs);

Expression operator-(const Expression& lhs, const Expression& rhs);
Expression operator-(const Expression& lhs, Expression&& rhs);
Expression operator-(Expression&& lhs, const Expression& rhs);
Expression operator-(Expression&& lhs, Expression&& rhs);
// NOLINTNEXTLINE(runtime/references) per C++ standard signature.
Expression& operator-=(Expression& lhs, const Expression& rhs);

Expression operator+(const Expression& e);

Expression operator-(const Expression& e);
Expression operator-(Expression&& e);

Expression operator*(const Expression& lhs, const Expression& rhs);
Expression operator*(const Expression& lhs, Expression&& rhs);
Expression operator*(Expression&& lhs, const Expression& rhs);
Expression operator*(Expression&& lhs, Expression&& rhs);
// NOLINTNEXTLINE(runtime/references) per C++ standard signature.
Expression& operator*=(Expression& lhs, const Expression& rhs);

Expression operator/(Expression lhs, const Expression& rhs);
// NOLINTNEXTLINE(runtime/references) per C++ standard signature.
Expression& operator/=(Expression& lhs, const Expression& rhs);

/// Creates an expression for (∑ᵢ expressionsᵢ).
/// @note When `expressions` is an empty vector, it returns Expression::Zero().
Expression Sum(const std::vector<Expression>& expressions);

/// Creates an expression for (∏ᵢ expressionsᵢ).
/// @note When `expressions` is an empty vector, it returns Expression::One().
Expression Prod(const std::vector<Expression>& expressions);

Expression real_constant(double lb, double ub, bool use_lb_as_representative);
Expression log(const Expression& e);
Expression abs(const Expression& e);
Expression exp(const Expression& e);
Expression sqrt(const Expression& e);
Expression pow(const Expression& e1, const Expression& e2);
Expression sin(const Expression& e);
Expression cos(const Expression& e);
Expression tan(const Expression& e);
Expression asin(const Expression& e);
Expression acos(const Expression& e);
Expression atan(const Expression& e);
Expression atan2(const Expression& e1, const Expression& e2);
Expression sinh(const Expression& e);
Expression cosh(const Expression& e);
Expression tanh(const Expression& e);
Expression min(const Expression& e1, const Expression& e2);
Expression max(const Expression& e1, const Expression& e2);
Expression if_then_else(const Formula& f_cond, const Expression& e_then,
                        const Expression& e_else);

/** Constructs an uninterpreted-function expression with @p name and @p vars.
 * An uninterpreted function is an opaque function that has no other property
 * than its name and a set of its arguments. This is useful to applications
 * where it is good enough to provide abstract information of a function without
 * exposing full details. Declaring sparsity of a system is a typical example.
 *
 * See also `FunctionalForm::Arbitrary(Variables v)` which shares the same
 * motivation.
 */
Expression uninterpreted_function(const std::string& name,
                                  const Variables& vars);
void swap(Expression& a, Expression& b);

std::ostream& operator<<(std::ostream& os, const Expression& e);

/** Checks if @p e is a floating-point constant expression. */
bool is_constant(const Expression& e);
/** Checks if @p e is a floating-point constant expression representing @p v. */
bool is_constant(const Expression& e, double v);
/** Checks if @p e is a real constant expression. */
bool is_real_constant(const Expression& e);
/** Checks if @p e is 0.0. */
bool is_zero(const Expression& e);
/** Checks if @p e is 1.0. */
bool is_one(const Expression& e);
/** Checks if @p e is -1.0. */
bool is_neg_one(const Expression& e);
/** Checks if @p e is 2.0. */
bool is_two(const Expression& e);
/** Checks if @p e is NaN. */
bool is_nan(const Expression& e);
/** Checks if @p e is a variable expression. */
bool is_variable(const Expression& e);
/** Checks if @p e is an addition expression. */
bool is_addition(const Expression& e);
/** Checks if @p e is a multiplication expression. */
bool is_multiplication(const Expression& e);
/** Checks if @p e is a division expression. */
bool is_division(const Expression& e);
/** Checks if @p e is a log expression. */
bool is_log(const Expression& e);
/** Checks if @p e is an abs expression. */
bool is_abs(const Expression& e);
/** Checks if @p e is an exp expression. */
bool is_exp(const Expression& e);
/** Checks if @p e is a square-root expression. */
bool is_sqrt(const Expression& e);
/** Checks if @p e is a power-function expression. */
bool is_pow(const Expression& e);
/** Checks if @p e is a sine expression. */
bool is_sin(const Expression& e);
/** Checks if @p e is a cosine expression. */
bool is_cos(const Expression& e);
/** Checks if @p e is a tangent expression. */
bool is_tan(const Expression& e);
/** Checks if @p e is an arcsine expression. */
bool is_asin(const Expression& e);
/** Checks if @p e is an arccosine expression. */
bool is_acos(const Expression& e);
/** Checks if @p e is an arctangent expression. */
bool is_atan(const Expression& e);
/** Checks if @p e is an arctangent2 expression. */
bool is_atan2(const Expression& e);
/** Checks if @p e is a hyperbolic-sine expression. */
bool is_sinh(const Expression& e);
/** Checks if @p e is a hyperbolic-cosine expression. */
bool is_cosh(const Expression& e);
/** Checks if @p e is a hyperbolic-tangent expression. */
bool is_tanh(const Expression& e);
/** Checks if @p e is a min expression. */
bool is_min(const Expression& e);
/** Checks if @p e is a max expression. */
bool is_max(const Expression& e);
/** Checks if @p e is an if-then-else expression. */
bool is_if_then_else(const Expression& e);
/** Checks if @p e is an uninterpreted-function expression. */
bool is_uninterpreted_function(const Expression& e);

/** Returns the constant value of the floating-point constant expression @p e.
 *  @pre @p e is either a floating-point constant or real constant expression.
 */
double get_constant_value(const Expression& e);
/** Returns the lower-bound of the floating-point constant expression @p e.
 *  @pre @p e is a real constant expression.
 */
double get_lb_of_real_constant(const Expression& e);
/** Returns the upper-bound of the floating-point constant expression @p e.
 *  @pre @p e is a real constant expression.
 */
double get_ub_of_real_constant(const Expression& e);
/** Returns the embedded variable in the variable expression @p e.
 *  @pre @p e is a variable expression.
 */
const Variable& get_variable(const Expression& e);
/** Returns the argument in the unary expression @p e.
 *  @pre @p e is a unary expression.
 */
const Expression& get_argument(const Expression& e);
/** Returns the first argument of the binary expression @p e.
 *  @pre @p e is a binary expression.
 */
const Expression& get_first_argument(const Expression& e);
/** Returns the second argument of the binary expression @p e.
 *  @pre @p e is a binary expression.
 */
const Expression& get_second_argument(const Expression& e);
/** Returns the constant part of the addition expression @p e. For instance,
 *  given 7 + 2 * x + 3 * y, it returns 7.
 *  @pre @p e is an addition expression.
 */
double get_constant_in_addition(const Expression& e);
/** Returns the map from an expression to its coefficient in the addition
 *  expression @p e. For instance, given 7 + 2 * x + 3 * y, the return value
 *  maps 'x' to 2 and 'y' to 3.
 *  @pre @p e is an addition expression.
 */
const std::map<Expression, double>& get_expr_to_coeff_map_in_addition(
    const Expression& e);
/** Returns the constant part of the multiplication expression @p e. For
 *  instance, given 7 * x^2 * y^3, it returns 7.
 *  @pre @p e is a multiplication expression.
 */
double get_constant_in_multiplication(const Expression& e);
/** Returns the map from a base expression to its exponent expression in the
 * multiplication expression @p e. For instance, given 7 * x^2 * y^3 * z^x, the
 * return value maps 'x' to 2, 'y' to 3, and 'z' to 'x'.
 *  @pre @p e is a multiplication expression.
 */
const std::map<Expression, Expression>&
get_base_to_exponent_map_in_multiplication(const Expression& e);

/** Returns the conditional formula in the if-then-else expression @p e.
 * @pre @p e is an if-then-else expression.
 */
const Formula& get_conditional_formula(const Expression& e);

/** Returns the 'then' expression in the if-then-else expression @p e.
 * @pre @p e is an if-then-else expression.
 */
const Expression& get_then_expression(const Expression& e);

/** Returns the 'else' expression in the if-then-else expression @p e.
 * @pre @p e is an if-then-else expression.
 */
const Expression& get_else_expression(const Expression& e);

/** Returns the name of an uninterpreted-function expression @p e.
 *  @pre @p e is an uninterpreted-function expression.
 */
const std::string& get_uninterpreted_function_name(const Expression& e);

Expression operator+(const Variable& var);
Expression operator-(const Variable& var);

}  // namespace symbolic

/** Computes the hash value of a symbolic expression. */
template <>
struct hash_value<symbolic::Expression> {
  size_t operator()(const symbolic::Expression& e) const {
    return e.get_hash();
  }
};

}  // namespace drake
}  // namespace dreal

namespace std {
/* Provides std::less<dreal::drake::symbolic::Expression>. */
template <>
struct less<dreal::drake::symbolic::Expression> {
  bool operator()(const dreal::drake::symbolic::Expression& lhs,
                  const dreal::drake::symbolic::Expression& rhs) const {
    return lhs.Less(rhs);
  }
};

/* Provides std::equal_to<dreal::drake::symbolic::Expression>. */
template <>
struct equal_to<dreal::drake::symbolic::Expression> {
  bool operator()(const dreal::drake::symbolic::Expression& lhs,
                  const dreal::drake::symbolic::Expression& rhs) const {
    return lhs.EqualTo(rhs);
  }
};

template <>
struct hash<dreal::drake::symbolic::Expression> {
  size_t operator()(const dreal::drake::symbolic::Expression& e) const {
    return e.get_hash();
  }
};

/* Provides std::numeric_limits<dreal::drake::symbolic::Expression>. */
template <>
struct numeric_limits<dreal::drake::symbolic::Expression>
    : public numeric_limits<double> {};

}  // namespace std
