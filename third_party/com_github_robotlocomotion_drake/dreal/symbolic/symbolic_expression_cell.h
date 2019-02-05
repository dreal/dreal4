#pragma once

#include <algorithm>  // for cpplint only
#include <atomic>
#include <cstddef>
#include <map>
#include <ostream>
#include <string>

#include "dreal/symbolic/symbolic_environment.h"
#include "dreal/symbolic/symbolic_expression.h"
#include "dreal/symbolic/symbolic_formula.h"
#include "dreal/symbolic/symbolic_variable.h"
#include "dreal/symbolic/symbolic_variables.h"

namespace dreal {
namespace drake {
namespace symbolic {

/** Represents an abstract class which is the base of concrete
 * symbolic-expression classes.
 *
 * @note It provides virtual function, ExpressionCell::Display, because
 * operator<< is not allowed to be a virtual function.
 */
class ExpressionCell {
 public:
  /** Returns expression kind. */
  ExpressionKind get_kind() const { return kind_; }

  /** Returns hash value. */
  size_t get_hash() const { return hash_; }

  /** Collects variables in expression. */
  virtual Variables GetVariables() const = 0;

  /** Checks structural equality. */
  virtual bool EqualTo(const ExpressionCell& c) const = 0;

  /** Provides lexicographical ordering between expressions. */
  virtual bool Less(const ExpressionCell& c) const = 0;

  /** Checks if this symbolic expression is convertible to Polynomial. */
  bool is_polynomial() const { return is_polynomial_; }

  /** Evaluates under a given environment (by default, an empty environment).
   *  @throws std::runtime_error if NaN is detected during evaluation.
   */
  virtual double Evaluate(const Environment& env) const = 0;

  /** Expands out products and positive integer powers in expression.
   * @throws std::runtime_error if NaN is detected during expansion.
   */
  virtual Expression Expand() = 0;

  /** Returns an Expression obtained by replacing all occurrences of the
   * variables in @p s in the current expression cell with the corresponding
   * expressions in @p s.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  virtual Expression Substitute(const ExpressionSubstitution& expr_subst,
                                const FormulaSubstitution& formula_subst) = 0;

  /** Differentiates this symbolic expression with respect to the variable @p
   * var.
   * @throws std::runtime_error if it is not differentiable.
   */
  virtual Expression Differentiate(const Variable& x) const = 0;

  /** Outputs string representation of expression into output stream @p os. */
  virtual std::ostream& Display(std::ostream& os) const = 0;

  /** Returns the reference count of this cell. */
  unsigned use_count() const { return rc_; }

  /** Copy-constructs an ExpressionCell from an lvalue. (DELETED) */
  ExpressionCell(const ExpressionCell& e) = delete;

  /** Move-constructs an ExpressionCell from an rvalue. (DELETED) */
  ExpressionCell(ExpressionCell&& e) = delete;

  /** Move-assigns (DELETED). */
  ExpressionCell& operator=(ExpressionCell&& e) = delete;

  /** Copy-assigns (DELETED). */
  ExpressionCell& operator=(const ExpressionCell& e) = delete;

 protected:
  /** Default constructor. */
  ExpressionCell() = default;
  /** Constructs ExpressionCell of kind @p k with @p hash and @p is_poly . */
  ExpressionCell(ExpressionKind k, size_t hash, bool is_poly);
  /** Default destructor. */
  virtual ~ExpressionCell() = default;
  /** Returns an expression pointing to this ExpressionCell. */
  Expression GetExpression();

 private:
  const ExpressionKind kind_{};
  const size_t hash_{};
  const bool is_polynomial_{false};

  // Reference counter.
  mutable std::atomic<unsigned> rc_{0};
  void increase_rc() const { ++rc_; }
  size_t decrease_rc() const {
    if (--rc_ == 0) {
      delete this;
      return 0;
    } else {
      return rc_;
    }
  }

  // So that Expression can call {increase,decrease}_rc.
  friend Expression;
};

/** Represents the base class for unary expressions.  */
class UnaryExpressionCell : public ExpressionCell {
 public:
  Variables GetVariables() const override;
  bool EqualTo(const ExpressionCell& e) const override;
  bool Less(const ExpressionCell& e) const override;
  double Evaluate(const Environment& env) const override;
  /** Returns the argument. */
  const Expression& get_argument() const { return e_; }

  /** Copy-constructs from an lvalue. (DELETED) */
  UnaryExpressionCell(const UnaryExpressionCell& e) = delete;

  /** Default constructor (DELETED). */
  UnaryExpressionCell() = delete;

  /** Move-assigns (DELETED). */
  UnaryExpressionCell& operator=(UnaryExpressionCell&& e) = delete;

  /** Copy-assigns (DELETED). */
  UnaryExpressionCell& operator=(const UnaryExpressionCell& e) = delete;

  /** Move-constructs from an rvalue. (DELETED) */
  UnaryExpressionCell(UnaryExpressionCell&& e) = delete;

  /** Default destructor. */
  ~UnaryExpressionCell() override = default;

 protected:

  /** Constructs UnaryExpressionCell of kind @p k with @p hash, @p e, and @p
   * is_poly. */
  UnaryExpressionCell(ExpressionKind k, const Expression& e, bool is_poly);
  /** Returns the evaluation result f(@p v ). */
  virtual double DoEvaluate(double v) const = 0;

 private:
  const Expression e_;
};

/** Represents the base class for binary expressions.
 */
class BinaryExpressionCell : public ExpressionCell {
 public:
  Variables GetVariables() const override;
  bool EqualTo(const ExpressionCell& e) const override;
  bool Less(const ExpressionCell& e) const override;
  double Evaluate(const Environment& env) const override;
  /** Returns the first argument. */
  const Expression& get_first_argument() const { return e1_; }
  /** Returns the second argument. */
  const Expression& get_second_argument() const { return e2_; }

  /** Copy-constructs from an lvalue. (DELETED) */
  BinaryExpressionCell(const BinaryExpressionCell& e) = delete;

  /** Move-constructs from an rvalue. (DELETED) */
  BinaryExpressionCell(BinaryExpressionCell&& e) = delete;

  /** Default constructor (DELETED). */
  BinaryExpressionCell() = delete;

  /** Move-assigns (DELETED). */
  BinaryExpressionCell& operator=(BinaryExpressionCell&& e) = delete;

  /** Copy-assigns (DELETED). */
  BinaryExpressionCell& operator=(const BinaryExpressionCell& e) = delete;

  /** Default destructor. */
  ~BinaryExpressionCell() override = default;

 protected:
  /** Constructs BinaryExpressionCell of kind @p k with @p hash, @p e1, @p e2,
   * @p is_poly.
   */
  BinaryExpressionCell(ExpressionKind k, const Expression& e1,
                       const Expression& e2, bool is_poly);
  /** Returns the evaluation result f(@p v1, @p v2 ). */
  virtual double DoEvaluate(double v1, double v2) const = 0;

 private:
  const Expression e1_;
  const Expression e2_;
};

/** Symbolic expression representing a variable. */
class ExpressionVar : public ExpressionCell {
 public:
  /** Constructs an expression from @p var.
   * @pre @p var is neither a dummy nor a BOOLEAN variable.
   */
  explicit ExpressionVar(const Variable& v);
  const Variable& get_variable() const { return var_; }
  Variables GetVariables() const override;
  bool EqualTo(const ExpressionCell& e) const override;
  bool Less(const ExpressionCell& e) const override;
  double Evaluate(const Environment& env) const override;
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  const Variable var_;
};

/** Symbolic expression representing a floating-point constant (double). */
class ExpressionConstant : public ExpressionCell {
 public:
  explicit ExpressionConstant(double v);
  double get_value() const { return v_; }
  Variables GetVariables() const override;
  bool EqualTo(const ExpressionCell& e) const override;
  bool Less(const ExpressionCell& e) const override;
  double Evaluate(const Environment& env) const override;
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  const double v_{};
};

/** Symbolic expression representing a real constant represented by a
 * double interval [lb, ub].
 *
 * Note that the gap between lb and ub should be minimal, that is, the
 * next machine-representable number of `lb` should be `ub`.
 */
class ExpressionRealConstant : public ExpressionCell {
 public:
  ExpressionRealConstant(double lb, double ub, bool use_lb_as_representative);
  double get_lb() const { return lb_; }
  double get_ub() const { return ub_; }
  double get_value() const { return use_lb_as_representative_ ? lb_ : ub_; }
  Variables GetVariables() const override;
  bool EqualTo(const ExpressionCell& e) const override;
  bool Less(const ExpressionCell& e) const override;
  double Evaluate(const Environment& env) const override;
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  const double lb_{};
  const double ub_{};
  const bool use_lb_as_representative_{};
};

/** Symbolic expression representing NaN (not-a-number). */
class ExpressionNaN : public ExpressionCell {
 public:
  ExpressionNaN();
  Variables GetVariables() const override;
  bool EqualTo(const ExpressionCell& e) const override;
  bool Less(const ExpressionCell& e) const override;
  double Evaluate(const Environment& env) const override;
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;
};

/** Symbolic expression representing an addition which is a sum of products.
 *
 * @f[
 *     c_0 + \sum c_i * e_i
 * @f]
 *
 *  where @f$ c_i @f$ is a constant and @f$ e_i @f$ is a symbolic expression.
 *
 * Internally this class maintains a member variable @c constant_ to represent
 * @f$ c_0 @f$ and another member variable @c expr_to_coeff_map_ to represent a
 * mapping from an expression @f$ e_i @f$ to its coefficient @f$ c_i @f$ of
 * double.
 */
class ExpressionAdd : public ExpressionCell {
 public:
  /** Constructs ExpressionAdd from @p constant_term and @p term_to_coeff_map.
   */
  ExpressionAdd(double constant,
                std::map<Expression, double> expr_to_coeff_map);
  Variables GetVariables() const override;
  bool EqualTo(const ExpressionCell& e) const override;
  bool Less(const ExpressionCell& e) const override;
  double Evaluate(const Environment& env) const override;
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;
  /** Returns the constant. */
  double get_constant() const { return constant_; }
  /** Returns map from an expression to its coefficient. */
  const std::map<Expression, double>& get_expr_to_coeff_map() const {
    return expr_to_coeff_map_;
  }

  // TODO(soonho): Make the following private and allow
  // only selected functions/method to use them.
  /** Returns map from an expression to its coefficient. */
  std::map<Expression, double>& get_mutable_expr_to_coeff_map() {
    return expr_to_coeff_map_;
  }

 private:
  std::ostream& DisplayTerm(std::ostream& os, bool print_plus, double coeff,
                            const Expression& term) const;

  double constant_{};
  std::map<Expression, double> expr_to_coeff_map_;
};

/** Factory class to help build ExpressionAdd expressions.
 *
 * @note Once `GetExpression()` is called and an expression is
 * generated, this class should not be used again. If another
 * `GetExpression()` is called, it will throws an exception.
 */
class ExpressionAddFactory {
 public:
  ExpressionAddFactory(const ExpressionAddFactory&) = default;
  ExpressionAddFactory& operator=(const ExpressionAddFactory&) = default;
  ExpressionAddFactory(ExpressionAddFactory&&) = default;
  ExpressionAddFactory& operator=(ExpressionAddFactory&&) = default;

  /** Default constructor. */
  ExpressionAddFactory() = default;

  /** Default destructor. */
  ~ExpressionAddFactory() = default;

  /** Constructs ExpressionAddFactory with @p constant and @p
   * expr_to_coeff_map. */
  ExpressionAddFactory(double constant,
                       std::map<Expression, double> expr_to_coeff_map);

  /** Constructs ExpressionAddFactory from @p ptr. */
  explicit ExpressionAddFactory(const ExpressionAdd* ptr);

  /** Adds @p e to this factory. */
  ExpressionAddFactory& AddExpression(const Expression& e);
  /** Adds ExpressionAdd pointed by @p ptr to this factory. */
  ExpressionAddFactory& Add(const ExpressionAdd* ptr);
  /** Assigns a factory from a pointer to ExpressionAdd.  */
  ExpressionAddFactory& operator=(const ExpressionAdd* ptr);

  /** Negates the expressions in factory.
   * If it represents c0 + c1 * t1 + ... + * cn * tn,
   * this method flips it into -c0 - c1 * t1 - ... - cn * tn.
   * @returns *this.
   */
  ExpressionAddFactory& Negate();
  /** Returns a symbolic expression. */
  Expression GetExpression();

 private:
  /* Adds constant to this factory.
   * Adding constant constant into an add factory representing
   *
   *     c0 + c1 * t1 + ... + cn * tn
   *
   * results in (c0 + constant) + c1 * t1 + ... + cn * tn.  */
  ExpressionAddFactory& AddConstant(double constant);
  /* Adds coeff * term to this factory.
   *
   * Adding (coeff * term) into an add factory representing
   *
   *     c0 + c1 * t1 + ... + cn * tn
   *
   * results in c0 + c1 * t1 + ... + (coeff * term) + ... + cn * tn. Note that
   * it also performs simplifications to merge the coefficients of common terms.
   */
  ExpressionAddFactory& AddTerm(double coeff, const Expression& term);
  /* Adds expr_to_coeff_map to this factory. It calls AddConstant and AddTerm
   * methods. */
  ExpressionAddFactory& AddMap(
      const std::map<Expression, double>& expr_to_coeff_map);

  bool get_expression_is_called_{false};
  double constant_{0.0};
  std::map<Expression, double> expr_to_coeff_map_;
};

/** Symbolic expression representing a multiplication of powers.
 *
 * @f[
 *     c_0 \cdot \prod b_i^{e_i}
 * @f]
 *
 * where @f$ c_0 @f$ is a constant and @f$ b_i @f$ and @f$ e_i @f$ are symbolic
 * expressions.
 *
 * Internally this class maintains a member variable @c constant_ representing
 * @f$ c_0 @f$ and another member variable @c base_to_exponent_map_ representing
 * a mapping from a base, @f$ b_i @f$ to its exponentiation @f$ e_i @f$.
 */
class ExpressionMul : public ExpressionCell {
 public:
  /** Constructs ExpressionMul from @p constant and @p base_to_exponent_map. */
  ExpressionMul(double constant,
                std::map<Expression, Expression> base_to_exponent_map);
  Variables GetVariables() const override;
  bool EqualTo(const ExpressionCell& e) const override;
  bool Less(const ExpressionCell& e) const override;
  double Evaluate(const Environment& env) const override;
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;
  /** Returns constant term. */
  double get_constant() const { return constant_; }
  /** Returns map from a term to its exponent. */
  const std::map<Expression, Expression>& get_base_to_exponent_map() const {
    return base_to_exponent_map_;
  }

  // TODO(soonho): Make the following private and allow
  // only selected functions/method to use them.
  /** Returns map from a term to its exponent. */
  std::map<Expression, Expression>& get_mutable_base_to_exponent_map() {
    return base_to_exponent_map_;
  }

 private:
  std::ostream& DisplayTerm(std::ostream& os, bool print_mul,
                            const Expression& base,
                            const Expression& exponent) const;

  double constant_{};
  std::map<Expression, Expression> base_to_exponent_map_;
};

/** Factory class to help build ExpressionMul expressions.
 *
 * @note Once `GetExpression()` is called and an expression is
 * generated, this class should not be used again. If another
 * `GetExpression()` is called, it will throws an exception.
 */
class ExpressionMulFactory {
 public:
  ExpressionMulFactory(const ExpressionMulFactory&) = default;
  ExpressionMulFactory& operator=(const ExpressionMulFactory&) = default;
  ExpressionMulFactory(ExpressionMulFactory&&) = default;
  ExpressionMulFactory& operator=(ExpressionMulFactory&&) = default;

  /** Default constructor. It constructs. */
  ExpressionMulFactory() = default;

  /** Default destructor. */
  ~ExpressionMulFactory() = default;

  /** Constructs ExpressionMulFactory with @p constant and @p
   * base_to_exponent_map. */
  ExpressionMulFactory(double constant,
                       std::map<Expression, Expression> base_to_exponent_map);

  /** Constructs ExpressionMulFactory from @p ptr. */
  explicit ExpressionMulFactory(const ExpressionMul* ptr);

  /** Adds @p e to this factory. */
  ExpressionMulFactory& AddExpression(const Expression& e);
  /** Adds ExpressionMul pointed by @p ptr to this factory. */
  ExpressionMulFactory& Add(const ExpressionMul* ptr);
  /** Assigns a factory from a pointer to ExpressionMul.  */
  ExpressionMulFactory& operator=(const ExpressionMul* ptr);
  /** Negates the expressions in factory.
   * If it represents c0 * p1 * ... * pn,
   * this method flips it into -c0 * p1 * ... * pn.
   * @returns *this.
   */
  ExpressionMulFactory& Negate();
  /** Returns a symbolic expression. */
  Expression GetExpression();

 private:
  /* Adds constant to this factory.
     Adding constant into an mul factory representing

         c * b1 ^ e1 * ... * bn ^ en

     results in (constant * c) * b1 ^ e1 * ... * bn ^ en. */
  ExpressionMulFactory& AddConstant(double constant);
  /* Adds pow(base, exponent) to this factory.
     Adding pow(base, exponent) into an mul factory representing

         c * b1 ^ e1 * ... * bn ^ en

     results in c * b1 ^ e1 * ... * base^exponent * ... * bn ^ en. Note that
     it also performs simplifications to merge the exponents of common bases.
  */
  ExpressionMulFactory& AddTerm(const Expression& base,
                                const Expression& exponent);
  /* Adds base_to_exponent_map to this factory. It calls AddConstant and AddTerm
   * methods. */
  ExpressionMulFactory& AddMap(
      const std::map<Expression, Expression>& base_to_exponent_map);

  bool get_expression_is_called_{false};
  double constant_{1.0};
  std::map<Expression, Expression> base_to_exponent_map_;
};

/** Symbolic expression representing division. */
class ExpressionDiv : public BinaryExpressionCell {
 public:
  ExpressionDiv(const Expression& e1, const Expression& e2);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v1, double v2) const override;
};

/** Symbolic expression representing logarithms. */
class ExpressionLog : public UnaryExpressionCell {
 public:
  explicit ExpressionLog(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

  friend Expression log(const Expression& e);

 private:
  /* Throws std::domain_error if v ∉ [0, +oo). */
  static void check_domain(double v);
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing absolute value function. */
class ExpressionAbs : public UnaryExpressionCell {
 public:
  explicit ExpressionAbs(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

  friend Expression abs(const Expression& e);

 private:
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing exponentiation using the base of
 * natural logarithms. */
class ExpressionExp : public UnaryExpressionCell {
 public:
  explicit ExpressionExp(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing square-root. */
class ExpressionSqrt : public UnaryExpressionCell {
 public:
  explicit ExpressionSqrt(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

  friend Expression sqrt(const Expression& e);

 private:
  /* Throws std::domain_error if v ∉ [0, +oo). */
  static void check_domain(double v);
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing power function. */
class ExpressionPow : public BinaryExpressionCell {
 public:
  ExpressionPow(const Expression& e1, const Expression& e2);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

  friend Expression pow(const Expression& e1, const Expression& e2);

 private:
  /* Throws std::domain_error if v1 is finite negative and v2 is finite
     non-integer. */
  static void check_domain(double v1, double v2);
  double DoEvaluate(double v1, double v2) const override;
};

/** Symbolic expression representing sine function. */
class ExpressionSin : public UnaryExpressionCell {
 public:
  explicit ExpressionSin(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing cosine function. */
class ExpressionCos : public UnaryExpressionCell {
 public:
  explicit ExpressionCos(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing tangent function. */
class ExpressionTan : public UnaryExpressionCell {
 public:
  explicit ExpressionTan(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing arcsine function. */
class ExpressionAsin : public UnaryExpressionCell {
 public:
  explicit ExpressionAsin(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

  friend Expression asin(const Expression& e);

 private:
  /* Throws std::domain_error if v ∉ [-1.0, +1.0]. */
  static void check_domain(double v);
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing arccosine function. */
class ExpressionAcos : public UnaryExpressionCell {
 public:
  explicit ExpressionAcos(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

  friend Expression acos(const Expression& e);

 private:
  /* Throws std::domain_error if v ∉ [-1.0, +1.0]. */
  static void check_domain(double v);
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing arctangent function. */
class ExpressionAtan : public UnaryExpressionCell {
 public:
  explicit ExpressionAtan(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing atan2 function (arctangent function with
 * two arguments). atan2(y, x) is defined as atan(y/x). */
class ExpressionAtan2 : public BinaryExpressionCell {
 public:
  ExpressionAtan2(const Expression& e1, const Expression& e2);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v1, double v2) const override;
};

/** Symbolic expression representing hyperbolic sine function. */
class ExpressionSinh : public UnaryExpressionCell {
 public:
  explicit ExpressionSinh(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing hyperbolic cosine function. */
class ExpressionCosh : public UnaryExpressionCell {
 public:
  explicit ExpressionCosh(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing hyperbolic tangent function. */
class ExpressionTanh : public UnaryExpressionCell {
 public:
  explicit ExpressionTanh(const Expression& e);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v) const override;
};

/** Symbolic expression representing min function. */
class ExpressionMin : public BinaryExpressionCell {
 public:
  ExpressionMin(const Expression& e1, const Expression& e2);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v1, double v2) const override;
};

/** Symbolic expression representing max function. */
class ExpressionMax : public BinaryExpressionCell {
 public:
  ExpressionMax(const Expression& e1, const Expression& e2);
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

 private:
  double DoEvaluate(double v1, double v2) const override;
};

/** Symbolic expression representing if-then-else expression.  */
class ExpressionIfThenElse : public ExpressionCell {
 public:
  /** Constructs if-then-else expression from @p f_cond, @p e_then, and @p
   * e_else. */
  ExpressionIfThenElse(const Formula& f_cond, const Expression& e_then,
                       const Expression& e_else);
  Variables GetVariables() const override;
  bool EqualTo(const ExpressionCell& e) const override;
  bool Less(const ExpressionCell& e) const override;
  double Evaluate(const Environment& env) const override;
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

  /** Returns the conditional formula. */
  const Formula& get_conditional_formula() const { return f_cond_; }
  /** Returns the 'then' expression. */
  const Expression& get_then_expression() const { return e_then_; }
  /** Returns the 'else' expression. */
  const Expression& get_else_expression() const { return e_else_; }

 private:
  const Formula f_cond_;
  const Expression e_then_;
  const Expression e_else_;
};

/** Symbolic expression representing an uninterpreted function. */
class ExpressionUninterpretedFunction : public ExpressionCell {
 public:
  /** Constructs an uninterpreted-function expression from @p name and @p vars.
   */
  ExpressionUninterpretedFunction(const std::string& name,
                                  const Variables& vars);
  Variables GetVariables() const override;
  bool EqualTo(const ExpressionCell& e) const override;
  bool Less(const ExpressionCell& e) const override;
  double Evaluate(const Environment& env) const override;
  Expression Expand() override;
  Expression Substitute(const ExpressionSubstitution& expr_subst,
                        const FormulaSubstitution& formula_subst) override;
  Expression Differentiate(const Variable& x) const override;
  std::ostream& Display(std::ostream& os) const override;

  /** Returns the name of this expression. */
  const std::string& get_name() const { return name_; }

 private:
  const std::string name_;
  const Variables variables_;
};

/** Checks if @p c is a floating-point constant expression. */
bool is_constant(const ExpressionCell& c);
/** Checks if @p c is a real constant expression. */
bool is_real_constant(const ExpressionCell& c);
/** Checks if @p c is a variable expression. */
bool is_variable(const ExpressionCell& c);
/** Checks if @p c is an addition expression. */
bool is_addition(const ExpressionCell& c);
/** Checks if @p c is an multiplication expression. */
bool is_multiplication(const ExpressionCell& c);
/** Checks if @p c is a division expression. */
bool is_division(const ExpressionCell& c);
/** Checks if @p c is a log expression. */
bool is_log(const ExpressionCell& c);
/** Checks if @p c is an absolute-value-function expression. */
bool is_abs(const ExpressionCell& c);
/** Checks if @p c is an exp expression. */
bool is_exp(const ExpressionCell& c);
/** Checks if @p c is a square-root expression. */
bool is_sqrt(const ExpressionCell& c);
/** Checks if @p c is a power-function expression. */
bool is_pow(const ExpressionCell& c);
/** Checks if @p c is a sine expression. */
bool is_sin(const ExpressionCell& c);
/** Checks if @p c is a cosine expression. */
bool is_cos(const ExpressionCell& c);
/** Checks if @p c is a tangent expression. */
bool is_tan(const ExpressionCell& c);
/** Checks if @p c is an arcsine expression. */
bool is_asin(const ExpressionCell& c);
/** Checks if @p c is an arccosine expression. */
bool is_acos(const ExpressionCell& c);
/** Checks if @p c is an arctangent expression. */
bool is_atan(const ExpressionCell& c);
/** Checks if @p c is a arctangent2  expression. */
bool is_atan2(const ExpressionCell& c);
/** Checks if @p c is a hyperbolic-sine expression. */
bool is_sinh(const ExpressionCell& c);
/** Checks if @p c is a hyperbolic-cosine expression. */
bool is_cosh(const ExpressionCell& c);
/** Checks if @p c is a hyperbolic-tangent expression. */
bool is_tanh(const ExpressionCell& c);
/** Checks if @p c is a min expression. */
bool is_min(const ExpressionCell& c);
/** Checks if @p c is a max expression. */
bool is_max(const ExpressionCell& c);
/** Checks if @p c is an if-then-else expression. */
bool is_if_then_else(const ExpressionCell& c);
/** Checks if @p c is an uninterpreted-function expression. */
bool is_uninterpreted_function(const ExpressionCell& c);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionConstant*.
 *  @pre @p *expr_ptr is of @c ExpressionConstant.
 */
const ExpressionConstant* to_constant(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionConstant*.
 *  @pre @p *(e.ptr_) is of @c ExpressionConstant.
 */
const ExpressionConstant* to_constant(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionRealConstant*.
 *  @pre @p *expr_ptr is of @c ExpressionRealConstant.
 */
const ExpressionRealConstant* to_real_constant(
    const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionRealConstant*.
 *  @pre @p *(e.ptr_) is of @c ExpressionRealConstant.
 */
const ExpressionRealConstant* to_real_constant(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionVar*.
 *  @pre @p *expr_ptr is of @c ExpressionVar.
 */
const ExpressionVar* to_variable(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionVar*.
 *  @pre @p *(e.ptr_) is of @c ExpressionVar.
 */
const ExpressionVar* to_variable(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const UnaryExpressionCell*.
 *  @pre @c *expr_ptr is of @c UnaryExpressionCell.
 */
const UnaryExpressionCell* to_unary(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const UnaryExpressionCell*.
 *  @pre @c *(e.ptr_) is of @c UnaryExpressionCell.
 */
const UnaryExpressionCell* to_unary(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const BinaryExpressionCell*.
 *  @pre @c *expr_ptr is of @c BinaryExpressionCell.
 */
const BinaryExpressionCell* to_binary(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const BinaryExpressionCell*.
 *  @pre @c *(e.ptr_) is of @c BinaryExpressionCell.
 */
const BinaryExpressionCell* to_binary(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionAdd*.
 *  @pre @c *expr_ptr is of @c ExpressionAdd.
 */
const ExpressionAdd* to_addition(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionAdd*.
 *  @pre @c *(e.ptr_) is of @c ExpressionAdd.
 */
const ExpressionAdd* to_addition(const Expression& e);
/** Casts @p expr_ptr of ExpressionCell* to @c ExpressionAdd*.
 *  @pre @c *expr_ptr is of @c ExpressionAdd.
 */
ExpressionAdd* to_addition(ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c ExpressionAdd*.
 *  @pre @c *(e.ptr_) is of @c ExpressionAdd.
 */
ExpressionAdd* to_addition(Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionMul*.
 *  @pre @c *expr_ptr is of @c ExpressionMul.
 */
const ExpressionMul* to_multiplication(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionMul*.
 *  @pre @c *(e.ptr_) is of @c ExpressionMul.
 */
const ExpressionMul* to_multiplication(const Expression& e);
/** Casts @p expr_ptr of ExpressionCell* to @c ExpressionMul*.
 *  @pre @c *expr_ptr is of @c ExpressionMul.
 */
ExpressionMul* to_multiplication(ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c ExpressionMul*.
 *  @pre @c *(e.ptr_) is of @c ExpressionMul.
 */
ExpressionMul* to_multiplication(Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionDiv*.
 *  @pre @c *expr_ptr is of @c ExpressionDiv.
 */
const ExpressionDiv* to_division(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionDiv*.
 *  @pre @c *(e.ptr_) is of @c ExpressionDiv.
 */
const ExpressionDiv* to_division(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionLog*.
 *  @pre @c *expr_ptr is of @c ExpressionLog.
 */
const ExpressionLog* to_log(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionLog*.
 *  @pre @c *(e.ptr_) is of @c ExpressionLog.
 */
const ExpressionLog* to_log(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionExp*.
 *  @pre @c *expr_ptr is of @c ExpressionExp.
 */
const ExpressionExp* to_exp(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionExp*.
 *  @pre @c *(e.ptr_) is of @c ExpressionExp.
 */
const ExpressionExp* to_exp(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionAbs*.
 *  @pre @c *expr_ptr is of @c ExpressionAbs.
 */
const ExpressionAbs* to_abs(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionAbs*.
 *  @pre @c *(e.ptr_) is of @c ExpressionAbs.
 */
const ExpressionAbs* to_abs(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionExp*.
 *  @pre @c *expr_ptr is of @c ExpressionExp.
 */
const ExpressionExp* to_exp(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionExp*.
 *  @pre @c *(e.ptr_) is of @c ExpressionExp.
 */
const ExpressionExp* to_exp(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionSqrt*.
 *  @pre @c *expr_ptr is of @c ExpressionSqrt.
 */
const ExpressionSqrt* to_sqrt(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionSqrt*.
 *  @pre @c *(e.ptr_) is of @c ExpressionSqrt.
 */
const ExpressionSqrt* to_sqrt(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionPow*.
 *  @pre @c *expr_ptr is of @c ExpressionPow.
 */
const ExpressionPow* to_pow(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionPow*.
 *  @pre @c *(e.ptr_) is of @c ExpressionPow.
 */
const ExpressionPow* to_pow(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionSin*.
 *  @pre @c *expr_ptr is of @c ExpressionSin.
 */
const ExpressionSin* to_sin(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionSin*.
 *  @pre @c *(e.ptr_) is of @c ExpressionSin.
 */
const ExpressionSin* to_sin(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionCos*.
 *  @pre @c *expr_ptr is of @c ExpressionCos.
 */
const ExpressionCos* to_cos(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionCos*.
 *  @pre @c *(e.ptr_) is of @c ExpressionCos.
 */
const ExpressionCos* to_cos(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionTan*.
 *  @pre @c *expr_ptr is of @c ExpressionTan.
 */
const ExpressionTan* to_tan(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionTan*.
 *  @pre @c *(e.ptr_) is of @c ExpressionTan.
 */
const ExpressionTan* to_tan(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionAsin*.
 *  @pre @c *expr_ptr is of @c ExpressionAsin.
 */
const ExpressionAsin* to_asin(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionAsin*.
 *  @pre @c *(e.ptr_) is of @c ExpressionAsin.
 */
const ExpressionAsin* to_asin(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionAcos*.
 *  @pre @c *expr_ptr is of @c ExpressionAcos.
 */
const ExpressionAcos* to_acos(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionAcos*.
 *  @pre @c *(e.ptr_) is of @c ExpressionAcos.
 */
const ExpressionAcos* to_acos(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionAtan*.
 *  @pre @c *expr_ptr is of @c ExpressionAtan.
 */
const ExpressionAtan* to_atan(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionAtan*.
 *  @pre @c *(e.ptr_) is of @c ExpressionAtan.
 */
const ExpressionAtan* to_atan(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionAtan2*.
 *  @pre @c *expr_ptr is of @c ExpressionAtan2.
 */
const ExpressionAtan2* to_atan2(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionAtan2*.
 *  @pre @c *(e.ptr_) is of @c ExpressionAtan2.
 */
const ExpressionAtan2* to_atan2(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionSinh*.
 *  @pre @c *expr_ptr is of @c ExpressionSinh.
 */
const ExpressionSinh* to_sinh(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionSinh*.
 *  @pre @c *(e.ptr_) is of @c ExpressionSinh.
 */
const ExpressionSinh* to_sinh(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionCosh*.
 *  @pre @c *expr_ptr is of @c ExpressionCosh.
 */
const ExpressionCosh* to_cosh(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionCosh*.
 *  @pre @c *(e.ptr_) is of @c ExpressionCosh.
 */
const ExpressionCosh* to_cosh(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionTanh*.
 *  @pre @c *expr_ptr is of @c ExpressionTanh.
 */
const ExpressionTanh* to_tanh(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionTanh*.
 *  @pre @c *(e.ptr_) is of @c ExpressionTanh.
 */
const ExpressionTanh* to_tanh(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionMin*.
 *  @pre @c *expr_ptr is of @c ExpressionMin.
 */
const ExpressionMin* to_min(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionMin*.
 *  @pre @c *(e.ptr_) is of @c ExpressionMin.
 */
const ExpressionMin* to_min(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionMax*.
 *  @pre @c *expr_ptr is of @c ExpressionMax.
 */
const ExpressionMax* to_max(const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionMax*.
 *  @pre @c *(e.ptr_) is of @c ExpressionMax.
 */
const ExpressionMax* to_max(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to
 *  @c const ExpressionIfThenElse*.
 *  @pre @c *expr_ptr is of @c ExpressionIfThenElse.
 */
const ExpressionIfThenElse* to_if_then_else(
    const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to @c const ExpressionIfThenElse*.
 *  @pre @c *(e.ptr_) is of @c ExpressionIfThenElse.
 */
const ExpressionIfThenElse* to_if_then_else(const Expression& e);

/** Casts @p expr_ptr of const ExpressionCell* to `const
 * ExpressionUninterpretedFunction*`.
 *  @pre @c *expr_ptr is of @c ExpressionUninterpretedFunction.
 */
const ExpressionUninterpretedFunction* to_uninterpreted_function(
    const ExpressionCell* expr_ptr);
/** Casts @p e of Expression to `const ExpressionUninterpretedFunction*`.
 * @pre @c *(e.ptr_) is of @c ExpressionUninterpretedFunction.
 */
const ExpressionUninterpretedFunction* to_uninterpreted_function(
    const Expression& e);

}  // namespace symbolic
}  // namespace drake
}  // namespace dreal
