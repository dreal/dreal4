#include "dreal/symbolic/symbolic_expression.h"

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstddef>
#include <map>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include "dreal/symbolic/symbolic_environment.h"
#include "dreal/symbolic/symbolic_expression_cell.h"
#include "dreal/symbolic/symbolic_formula.h"
#include "dreal/symbolic/symbolic_variable.h"
#include "dreal/symbolic/symbolic_variables.h"

namespace dreal {
namespace drake {
namespace symbolic {

using std::map;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::runtime_error;
using std::string;
using std::vector;

bool operator<(ExpressionKind k1, ExpressionKind k2) {
  return static_cast<int>(k1) < static_cast<int>(k2);
}

namespace {

// Returns true if @p v is represented by `int`.
bool is_integer(const double v) {
  // v should be in [int_min, int_max].
  if (!((std::numeric_limits<int>::lowest() <= v) &&
        (v <= std::numeric_limits<int>::max()))) {
    return false;
  }
  double intpart;  // dummy variable
  return modf(v, &intpart) == 0.0;
}

// Negates an addition expression.
// - (E_1 + ... + E_n) => (-E_1 + ... + -E_n)
Expression NegateAddition(const ExpressionAdd* e) {
  return ExpressionAddFactory{e}.Negate().GetExpression();
}

// Negates an addition expression.
// - (E_1 + ... + E_n) => (-E_1 + ... + -E_n)
Expression NegateAddition(ExpressionAdd* e) {
  return ExpressionAddFactory{e->get_constant(),
                              std::move(e->get_mutable_expr_to_coeff_map())}
      .Negate()
      .GetExpression();
}

// Negates a multiplication expression.
// - (c0 * E_1 * ... * E_n) => (-c0 * E_1 * ... * E_n)
Expression NegateMultiplication(const ExpressionMul* e) {
  return ExpressionMulFactory{e}.Negate().GetExpression();
}

// Negates a multiplication expression.
// - (c0 * E_1 * ... * E_n) => (-c0 * E_1 * ... * E_n)
Expression NegateMultiplication(ExpressionMul* e) {
  return ExpressionMulFactory{e->get_constant(),
                              std::move(e->get_mutable_base_to_exponent_map())}
      .Negate()
      .GetExpression();
}

}  // namespace

Expression::Expression(const Expression& e) : ptr_{e.ptr_} {
  assert(ptr_ != nullptr);
  ptr_->increase_rc();
}

Expression& Expression::operator=(const Expression& e) {
  assert(e.ptr_ != nullptr);
  e.ptr_->increase_rc();
  if (ptr_) {
    ptr_->decrease_rc();
  }
  ptr_ = e.ptr_;
  return *this;
}

Expression::Expression(Expression&& e) noexcept : ptr_{e.ptr_} {
  assert(ptr_ != nullptr);
  e.ptr_ = nullptr;
}

Expression& Expression::operator=(Expression&& e) noexcept {
  assert(e.ptr_ != nullptr);
  if (ptr_) {
    ptr_->decrease_rc();
  }
  ptr_ = e.ptr_;
  e.ptr_ = nullptr;
  return *this;
}

Expression::~Expression() {
  if (ptr_) {
    ptr_->decrease_rc();
  }
}

Expression::Expression() : Expression{Zero().ptr_} {}

Expression::Expression(const Variable& var)
    : Expression{new ExpressionVar(var)} {}

ExpressionCell* Expression::make_cell(const double d) {
  if (std::isnan(d)) {
    return Expression::NaN().ptr_;
  }
  if (d == 0.0) {
    return Expression::Zero().ptr_;
  } else if (d == 1.0) {
    return Expression::One().ptr_;
  } else if (d == M_PI) {
    return Expression::Pi().ptr_;
  } else if (d == M_E) {
    return Expression::E().ptr_;
  } else {
    return new ExpressionConstant(d);
  }
}

Expression::Expression(const double d) : Expression{make_cell(d)} {}

Expression::Expression(ExpressionCell* ptr) : ptr_{ptr} {
  assert(ptr_ != nullptr);
  ptr_->increase_rc();
}

ExpressionKind Expression::get_kind() const {
  assert(ptr_ != nullptr);
  return ptr_->get_kind();
}
size_t Expression::get_hash() const {
  assert(ptr_ != nullptr);
  return ptr_->get_hash();
}

Expression Expression::Zero() {
  static const Expression zero{new ExpressionConstant{0.0}};
  return zero;
}

Expression Expression::One() {
  static const Expression one{new ExpressionConstant{1.0}};
  return one;
}

Expression Expression::Pi() {
  static const Expression pi{new ExpressionConstant{M_PI}};
  return pi;
}

Expression Expression::E() {
  static const Expression e{new ExpressionConstant{M_E}};
  return e;
}

Expression Expression::NaN() {
  static const Expression nan{new ExpressionNaN()};
  return nan;
}

const Variables& Expression::GetVariables() const {
  assert(ptr_ != nullptr);
  if (!variables_) {
    variables_ = std::make_shared<Variables>(ptr_->GetVariables());
  }
  return *variables_;
}

bool Expression::EqualTo(const Expression& e) const {
  assert(ptr_ != nullptr);
  assert(e.ptr_ != nullptr);
  if (ptr_ == e.ptr_) {
    return true;
  }
  if (get_kind() != e.get_kind()) {
    return false;
  }
  if (get_hash() != e.get_hash()) {
    return false;
  }
  // Same kind/hash, but it could be the result of hash collision,
  // check structural equality.
  return ptr_->EqualTo(*(e.ptr_));
}

bool Expression::Less(const Expression& e) const {
  assert(ptr_ != nullptr);
  assert(e.ptr_ != nullptr);
  if (ptr_ == e.ptr_) {
    return false;  // this equals to e, not less-than.
  }
  const ExpressionKind k1{get_kind()};
  const ExpressionKind k2{e.get_kind()};
  if (k1 < k2) {
    return true;
  }
  if (k2 < k1) {
    return false;
  }
  // k1 == k2
  return ptr_->Less(*(e.ptr_));
}

bool Expression::is_polynomial() const {
  assert(ptr_ != nullptr);
  return ptr_->is_polynomial();
}

double Expression::Evaluate(const Environment& env) const {
  assert(ptr_ != nullptr);
  return ptr_->Evaluate(env);
}

Expression Expression::EvaluatePartial(const Environment& env) const {
  if (env.empty()) {
    return *this;
  }
  ExpressionSubstitution subst;
  for (const pair<const Variable, double>& p : env) {
    subst.emplace(p.first, p.second);
  }
  return Substitute(subst);
}

Expression Expression::Expand() const {
  assert(ptr_ != nullptr);
  return ptr_->Expand();
}

Expression Expression::Substitute(const Variable& var,
                                  const Expression& e) const {
  assert(ptr_ != nullptr);
  return ptr_->Substitute({{var, e}}, FormulaSubstitution{});
}

Expression Expression::Substitute(
    const ExpressionSubstitution& expr_subst,
    const FormulaSubstitution& formula_subst) const {
  assert(ptr_ != nullptr);
  if (!expr_subst.empty() || !formula_subst.empty()) {
    return ptr_->Substitute(expr_subst, formula_subst);
  }
  return *this;
}

Expression Expression::Substitute(
    const ExpressionSubstitution& expr_subst) const {
  assert(ptr_ != nullptr);
  if (!expr_subst.empty()) {
    return ptr_->Substitute(expr_subst, FormulaSubstitution{});
  }
  return *this;
}

Expression Expression::Substitute(
    const FormulaSubstitution& formula_subst) const {
  assert(ptr_ != nullptr);
  if (!formula_subst.empty()) {
    return ptr_->Substitute(ExpressionSubstitution{}, formula_subst);
  }
  return *this;
}

Expression Expression::Differentiate(const Variable& x) const {
  assert(ptr_ != nullptr);
  return ptr_->Differentiate(x);
}

string Expression::to_string() const {
  ostringstream oss;
  oss << *this;
  return oss.str();
}

Expression operator+(const Expression& lhs, const Expression& rhs) {
  Expression lhs_copy{lhs};
  return lhs_copy += rhs;
}

Expression operator+(const Expression& lhs, Expression&& rhs) {
  return rhs += lhs;
}

Expression operator+(Expression&& lhs, const Expression& rhs) {
  return lhs += rhs;
}

Expression operator+(Expression&& lhs, Expression&& rhs) {
  if (is_addition(lhs) && is_addition(rhs)) {
    if (to_addition(rhs)->get_expr_to_coeff_map().size() >
        to_addition(lhs)->get_expr_to_coeff_map().size()) {
      return rhs += lhs;
    }
  }
  if (is_addition(rhs)) {
    return rhs += lhs;
  }
  return lhs += rhs;
}

// NOLINTNEXTLINE(runtime/references) per C++ standard signature.
Expression& operator+=(Expression& lhs, const Expression& rhs) {
  // Simplification: 0 + x => x
  if (is_zero(lhs)) {
    return lhs = rhs;
  }
  // Simplification: x + 0 => x
  if (is_zero(rhs)) {
    return lhs;
  }
  // Simplification: Expression(c1) + Expression(c2) => Expression(c1 + c2)
  if (is_constant(lhs) && is_constant(rhs)) {
    return lhs = get_constant_value(lhs) + get_constant_value(rhs);
  }

  // Simplification: flattening. To build a new expression, we use
  // ExpressionAddFactory which holds intermediate terms and does
  // simplifications internally.
  if (is_addition(lhs)) {
    if (lhs.ptr_->use_count() == 1) {
      return lhs =
                 ExpressionAddFactory{
                     get_constant_in_addition(lhs),
                     std::move(
                         to_addition(lhs)->get_mutable_expr_to_coeff_map())}
                     .AddExpression(rhs)
                     .GetExpression();
    } else {
      return lhs = ExpressionAddFactory{to_addition(lhs)}
                       .AddExpression(rhs)
                       .GetExpression();
    }
  }
  if (is_addition(rhs)) {
    // 2. lhs + (e_1 + ... + e_n)
    return lhs = ExpressionAddFactory{to_addition(rhs)}
                     .AddExpression(lhs)
                     .GetExpression();
  } else {
    // nothing to flatten: return lhs + rhs
    return lhs = ExpressionAddFactory{}
                     .AddExpression(lhs)
                     .AddExpression(rhs)
                     .GetExpression();
  }
}

Expression& Expression::operator++() {
  *this += Expression::One();
  return *this;
}

Expression Expression::operator++(int) {
  Expression copy(*this);
  ++*this;
  return copy;
}

Expression operator-(const Expression& lhs, const Expression& rhs) {
  Expression lhs_copy{lhs};
  return lhs_copy -= rhs;
}

Expression operator-(const Expression& lhs, Expression&& rhs) {
  return lhs + (-std::move(rhs));
}

Expression operator-(Expression&& lhs, const Expression& rhs) {
  return lhs -= rhs;
}

Expression operator-(Expression&& lhs, Expression&& rhs) {
  return std::move(lhs) + (-std::move(rhs));
}

// NOLINTNEXTLINE(runtime/references) per C++ standard signature.
Expression& operator-=(Expression& lhs, const Expression& rhs) {
  return lhs += -rhs;
}

Expression operator+(const Expression& e) { return e; }

Expression operator-(const Expression& e) {
  // Simplification: constant folding
  if (is_constant(e)) {
    return Expression{-get_constant_value(e)};
  }
  // Simplification: push '-' inside over '+'.
  // -(E_1 + ... + E_n) => (-E_1 + ... + -E_n)
  if (is_addition(e)) {
    return NegateAddition(to_addition(e));
  }
  // Simplification: push '-' inside over '*'.
  // -(c0 * E_1 * ... * E_n) => (-c0 * E_1 * ... * E_n)
  if (is_multiplication(e)) {
    return NegateMultiplication(to_multiplication(e));
  }
  return -1 * e;
}

Expression operator-(Expression&& e) {
  if (e.ptr_->use_count() == 1) {
    if (is_addition(e)) {
      return NegateAddition(to_addition(e));
    }
    if (is_multiplication(e)) {
      return NegateMultiplication(to_multiplication(e));
    }
  }
  return -e;
}

Expression& Expression::operator--() {
  *this -= Expression::One();
  return *this;
}

Expression Expression::operator--(int) {
  const Expression copy(*this);
  --*this;
  return copy;
}

Expression operator*(const Expression& lhs, const Expression& rhs) {
  Expression lhs_copy{lhs};
  lhs_copy *= rhs;
  return lhs_copy;
}

Expression operator*(const Expression& lhs, Expression&& rhs) {
  return rhs *= lhs;
}

Expression operator*(Expression&& lhs, const Expression& rhs) {
  return lhs *= rhs;
}

Expression operator*(Expression&& lhs, Expression&& rhs) {
  if (is_multiplication(lhs) && is_multiplication(rhs)) {
    if (to_multiplication(rhs)->get_base_to_exponent_map().size() >
        to_multiplication(lhs)->get_base_to_exponent_map().size()) {
      return rhs *= lhs;
    }
  }
  if (is_multiplication(rhs)) {
    return rhs *= lhs;
  }
  return lhs *= rhs;
}

// NOLINTNEXTLINE(runtime/references) per C++ standard signature.
Expression& operator*=(Expression& lhs, const Expression& rhs) {
  // Simplification: 1 * x => x
  if (is_one(lhs)) {
    lhs = rhs;
    return lhs;
  }
  // Simplification: x * 1 => x
  if (is_one(rhs)) {
    return lhs;
  }
  // Simplification: (E1 / E2) * (E3 / E4) => (E1 * E3) / (E2 * E4)
  if (is_division(lhs) && is_division(rhs)) {
    return lhs = (get_first_argument(lhs) * get_first_argument(rhs)) /
                 (get_second_argument(lhs) * get_second_argument(rhs));
  }
  // Simplification: lhs * (c / E) => (c * lhs) / E
  if (is_division(rhs) && is_constant(get_first_argument(rhs))) {
    return lhs = (get_first_argument(rhs) * lhs) / get_second_argument(rhs);
  }
  // Simplification: (c / E) * rhs => (c * rhs) / E
  if (is_division(lhs) && is_constant(get_first_argument(lhs))) {
    return lhs = (get_first_argument(lhs) * rhs) / get_second_argument(lhs);
  }
  if (is_neg_one(lhs)) {
    if (is_addition(rhs)) {
      // Simplification: push '-' inside over '+'.
      // -1 * (E_1 + ... + E_n) => (-E_1 + ... + -E_n)
      return lhs = NegateAddition(to_addition(rhs));
    }
    if (is_multiplication(rhs)) {
      // Simplification: push '-' inside over '*'.
      // -1 * (c0 * E_1 * ... * E_n) => (-c0 * E_1 * ... * E_n)
      return lhs = NegateMultiplication(to_multiplication(rhs));
    }
  }

  if (is_neg_one(rhs)) {
    if (is_addition(lhs)) {
      // Simplification: push '-' inside over '+'.
      // (E_1 + ... + E_n) * -1 => (-E_1 + ... + -E_n)
      return lhs = NegateAddition(to_addition(lhs));
    }
    if (is_multiplication(lhs)) {
      // Simplification: push '-' inside over '*'.
      // (c0 * E_1 * ... * E_n) * -1 => (-c0 * E_1 * ... * E_n)
      return lhs = NegateMultiplication(to_multiplication(lhs));
    }
  }

  // Simplification: 0 * E => 0
  // TODO(soonho-tri): This simplification is not sound since it cancels `E`
  // which might cause 0/0 during evaluation.
  if (is_zero(lhs)) {
    return lhs;
  }
  // Simplification: E * 0 => 0
  // TODO(soonho-tri): This simplification is not sound since it cancels `E`
  // which might cause 0/0 during evaluation.
  if (is_zero(rhs)) {
    return lhs = Expression::Zero();
  }
  if (is_constant(lhs) && is_constant(rhs)) {
    // Simplification: Expression(c1) * Expression(c2) => Expression(c1 * c2)
    return lhs = Expression{get_constant_value(lhs) * get_constant_value(rhs)};
  }

  // Pow-related simplifications.
  if (is_pow(lhs)) {
    const Expression& e1{get_first_argument(lhs)};
    if (is_pow(rhs)) {
      const Expression& e3{get_first_argument(rhs)};
      if (e1.EqualTo(e3)) {
        // Simplification: pow(e1, e2) * pow(e1, e4) => pow(e1, e2 + e4)
        const Expression& e2{get_second_argument(lhs)};
        const Expression& e4{get_second_argument(rhs)};
        lhs = pow(e1, e2 + e4);
        return lhs;
      }
    }
    if (e1.EqualTo(rhs)) {
      // Simplification: pow(e1, e2) * e1 => pow(e1, e2 + 1)
      const Expression& e2{get_second_argument(lhs)};
      lhs = pow(e1, e2 + 1);
      return lhs;
    }
  } else {
    if (is_pow(rhs)) {
      const Expression& e1{get_first_argument(rhs)};
      if (e1.EqualTo(lhs)) {
        // Simplification: (lhs * rhs == e1 * pow(e1, e2)) => pow(e1, 1 + e2)
        const Expression& e2{get_second_argument(rhs)};
        lhs = pow(e1, 1 + e2);
        return lhs;
      }
    }
  }

  // Simplification: flattening
  ExpressionMulFactory mul_factory{};
  if (is_multiplication(lhs)) {
    // (e_1 * ... * e_n) * rhs
    if (lhs.ptr_->use_count() == 1) {
      return lhs =
                 ExpressionMulFactory{
                     get_constant_in_multiplication(lhs),
                     std::move(to_multiplication(lhs)
                                   ->get_mutable_base_to_exponent_map())}
                     .AddExpression(rhs)
                     .GetExpression();
    } else {
      return lhs = ExpressionMulFactory{to_multiplication(lhs)}
                       .AddExpression(rhs)
                       .GetExpression();
    }
  } else {
    if (is_multiplication(rhs)) {
      // e_1 * (e_2 * ... * e_n) -> (e_2 * ... * e_n * e_1)
      //
      // Note that we do not preserve the original ordering because * is
      // associative.
      mul_factory = to_multiplication(rhs);
      mul_factory.AddExpression(lhs);
    } else {
      // Simplification: x * x => x^2 (=pow(x,2))
      if (lhs.EqualTo(rhs)) {
        lhs = pow(lhs, 2.0);
        return lhs;
      }
      // nothing to flatten
      mul_factory.AddExpression(lhs);
      mul_factory.AddExpression(rhs);
    }
  }
  lhs = mul_factory.GetExpression();
  return lhs;
}

Expression operator/(Expression lhs, const Expression& rhs) {
  lhs /= rhs;
  return lhs;
}

// NOLINTNEXTLINE(runtime/references) per C++ standard signature.
Expression& operator/=(Expression& lhs, const Expression& rhs) {
  // Simplification: x / 1 => x
  if (is_one(rhs)) {
    return lhs;
  }
  // Simplification: Expression(c1) / Expression(c2) => Expression(c1 / c2)
  if (is_constant(lhs) && is_constant(rhs)) {
    const double v1{get_constant_value(lhs)};
    const double v2{get_constant_value(rhs)};
    if (v2 == 0.0) {
      ostringstream oss{};
      oss << "Division by zero: " << v1 << "/" << v2;
      throw runtime_error(oss.str());
    }
    lhs = Expression{v1 / v2};
    return lhs;
  }
  // Simplification: E / E => 1
  // TODO(soonho-tri): This simplification is not sound since it cancels `E`
  // which might contain 0/0 problems.
  if (lhs.EqualTo(rhs)) {
    lhs = Expression::One();
    return lhs;
  }
  lhs = Expression{new ExpressionDiv(lhs, rhs)};
  return lhs;
}

ostream& operator<<(ostream& os, const Expression& e) {
  assert(e.ptr_ != nullptr);
  return e.ptr_->Display(os);
}

Expression Sum(const std::vector<Expression>& expressions) {
  if (expressions.empty()) {
    return Expression::Zero();
  }
  ExpressionAddFactory f;
  for (const Expression& e : expressions) {
    f.AddExpression(e);
  }
  return f.GetExpression();
}

Expression Prod(const std::vector<Expression>& expressions) {
  if (expressions.empty()) {
    return Expression::One();
  }
  ExpressionMulFactory f;
  for (const Expression& e : expressions) {
    f.AddExpression(e);
  }
  return f.GetExpression();
}

Expression real_constant(const double lb, const double ub,
                         const bool use_lb_as_representative) {
  return Expression{
      new ExpressionRealConstant(lb, ub, use_lb_as_representative)};
}

Expression log(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    const double v{get_constant_value(e)};
    ExpressionLog::check_domain(v);
    return Expression{std::log(v)};
  }
  return Expression{new ExpressionLog(e)};
}

Expression abs(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    return Expression{std::fabs(get_constant_value(e))};
  }
  return Expression{new ExpressionAbs(e)};
}

Expression exp(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    return Expression{std::exp(get_constant_value(e))};
  }
  return Expression{new ExpressionExp(e)};
}

Expression sqrt(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    const double v{get_constant_value(e)};
    ExpressionSqrt::check_domain(v);
    return Expression{std::sqrt(v)};
  }
  // Simplification: sqrt(pow(x, 2)) => abs(x)
  if (is_pow(e)) {
    if (is_two(get_second_argument(e))) {
      return abs(get_first_argument(e));
    }
  }
  return Expression{new ExpressionSqrt(e)};
}

Expression pow(const Expression& e1, const Expression& e2) {
  // Simplification
  if (is_constant(e2)) {
    const double v2{get_constant_value(e2)};
    if (is_constant(e1)) {
      // Constant folding
      const double v1{get_constant_value(e1)};
      ExpressionPow::check_domain(v1, v2);
      return Expression{std::pow(v1, v2)};
    }
    // pow(E, 0) => 1
    // TODO(soonho-tri): This simplification is not sound since it cancels `E`
    // which might contain 0/0 problems.
    if (v2 == 0.0) {
      return Expression::One();
    }
    // pow(E, 1) => E
    if (v2 == 1.0) {
      return e1;
    }
  }
  if (is_pow(e1) && is_constant(e2)) {
    // pow(base, exponent) ^ e2 => pow(base, exponent * e2)
    //
    // only if both of exponent and e2 are integers.
    const Expression& exponent{get_second_argument(e1)};
    const double v1{get_constant_value(exponent)};
    const double v2{get_constant_value(e2)};
    if (is_integer(v1) && is_integer(v2)) {
      const Expression& base{get_first_argument(e1)};
      return Expression{new ExpressionPow(base, v1 * v2)};
    }
  }
  return Expression{new ExpressionPow(e1, e2)};
}

Expression sin(const Expression& e) {
  // simplification: constant folding.
  if (is_constant(e)) {
    return Expression{std::sin(get_constant_value(e))};
  }
  return Expression{new ExpressionSin(e)};
}

Expression cos(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    return Expression{std::cos(get_constant_value(e))};
  }

  return Expression{new ExpressionCos(e)};
}

Expression tan(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    return Expression{std::tan(get_constant_value(e))};
  }
  return Expression{new ExpressionTan(e)};
}

Expression asin(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    const double v{get_constant_value(e)};
    ExpressionAsin::check_domain(v);
    return Expression{std::asin(v)};
  }
  return Expression{new ExpressionAsin(e)};
}

Expression acos(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    const double v{get_constant_value(e)};
    ExpressionAcos::check_domain(v);
    return Expression{std::acos(v)};
  }
  return Expression{new ExpressionAcos(e)};
}

Expression atan(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    return Expression{std::atan(get_constant_value(e))};
  }
  return Expression{new ExpressionAtan(e)};
}

Expression atan2(const Expression& e1, const Expression& e2) {
  // Simplification: constant folding.
  if (is_constant(e1) && is_constant(e2)) {
    return Expression{
        std::atan2(get_constant_value(e1), get_constant_value(e2))};
  }
  return Expression{new ExpressionAtan2(e1, e2)};
}

Expression sinh(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    return Expression{std::sinh(get_constant_value(e))};
  }
  return Expression{new ExpressionSinh(e)};
}

Expression cosh(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    return Expression{std::cosh(get_constant_value(e))};
  }
  return Expression{new ExpressionCosh(e)};
}

Expression tanh(const Expression& e) {
  // Simplification: constant folding.
  if (is_constant(e)) {
    return Expression{std::tanh(get_constant_value(e))};
  }
  return Expression{new ExpressionTanh(e)};
}

Expression min(const Expression& e1, const Expression& e2) {
  // simplification: min(x, x) => x
  if (e1.EqualTo(e2)) {
    return e1;
  }
  // Simplification: constant folding.
  if (is_constant(e1) && is_constant(e2)) {
    return Expression{std::min(get_constant_value(e1), get_constant_value(e2))};
  }
  return Expression{new ExpressionMin(e1, e2)};
}

Expression max(const Expression& e1, const Expression& e2) {
  // Simplification: max(x, x) => x
  if (e1.EqualTo(e2)) {
    return e1;
  }
  // Simplification: constant folding
  if (is_constant(e1) && is_constant(e2)) {
    return Expression{std::max(get_constant_value(e1), get_constant_value(e2))};
  }
  return Expression{new ExpressionMax(e1, e2)};
}

Expression if_then_else(const Formula& f_cond, const Expression& e_then,
                        const Expression& e_else) {
  // simplification:: if(true, e1, e2) => e1
  if (f_cond.EqualTo(Formula::True())) {
    return e_then;
  }
  // simplification:: if(false, e1, e2) => e2
  if (f_cond.EqualTo(Formula::False())) {
    return e_else;
  }
  return Expression{new ExpressionIfThenElse(f_cond, e_then, e_else)};
}

Expression uninterpreted_function(const string& name, const Variables& vars) {
  return Expression{new ExpressionUninterpretedFunction(name, vars)};
}

bool is_constant(const Expression& e) { return is_constant(*e.ptr_); }
bool is_constant(const Expression& e, const double v) {
  return is_constant(e) && (to_constant(e)->get_value() == v);
}
bool is_real_constant(const Expression& e) { return is_real_constant(*e.ptr_); }
bool is_zero(const Expression& e) { return is_constant(e, 0.0); }
bool is_one(const Expression& e) { return is_constant(e, 1.0); }
bool is_neg_one(const Expression& e) { return is_constant(e, -1.0); }
bool is_two(const Expression& e) { return is_constant(e, 2.0); }
bool is_nan(const Expression& e) { return e.get_kind() == ExpressionKind::NaN; }
bool is_variable(const Expression& e) { return is_variable(*e.ptr_); }
bool is_addition(const Expression& e) { return is_addition(*e.ptr_); }
bool is_multiplication(const Expression& e) {
  return is_multiplication(*e.ptr_);
}
bool is_division(const Expression& e) { return is_division(*e.ptr_); }
bool is_log(const Expression& e) { return is_log(*e.ptr_); }
bool is_abs(const Expression& e) { return is_abs(*e.ptr_); }
bool is_exp(const Expression& e) { return is_exp(*e.ptr_); }
bool is_sqrt(const Expression& e) { return is_sqrt(*e.ptr_); }
bool is_pow(const Expression& e) { return is_pow(*e.ptr_); }
bool is_sin(const Expression& e) { return is_sin(*e.ptr_); }
bool is_cos(const Expression& e) { return is_cos(*e.ptr_); }
bool is_tan(const Expression& e) { return is_tan(*e.ptr_); }
bool is_asin(const Expression& e) { return is_asin(*e.ptr_); }
bool is_acos(const Expression& e) { return is_acos(*e.ptr_); }
bool is_atan(const Expression& e) { return is_atan(*e.ptr_); }
bool is_atan2(const Expression& e) { return is_atan2(*e.ptr_); }
bool is_sinh(const Expression& e) { return is_sinh(*e.ptr_); }
bool is_cosh(const Expression& e) { return is_cosh(*e.ptr_); }
bool is_tanh(const Expression& e) { return is_tanh(*e.ptr_); }
bool is_min(const Expression& e) { return is_min(*e.ptr_); }
bool is_max(const Expression& e) { return is_max(*e.ptr_); }
bool is_if_then_else(const Expression& e) { return is_if_then_else(*e.ptr_); }
bool is_uninterpreted_function(const Expression& e) {
  return is_uninterpreted_function(*e.ptr_);
}

double get_constant_value(const Expression& e) {
  return is_constant(e) ? to_constant(e)->get_value()
                        : to_real_constant(e)->get_value();
}
double get_lb_of_real_constant(const Expression& e) {
  return to_real_constant(e)->get_lb();
}
double get_ub_of_real_constant(const Expression& e) {
  return to_real_constant(e)->get_ub();
}
const Variable& get_variable(const Expression& e) {
  return to_variable(e)->get_variable();
}
const Expression& get_argument(const Expression& e) {
  return to_unary(e)->get_argument();
}
const Expression& get_first_argument(const Expression& e) {
  return to_binary(e)->get_first_argument();
}
const Expression& get_second_argument(const Expression& e) {
  return to_binary(e)->get_second_argument();
}
double get_constant_in_addition(const Expression& e) {
  return to_addition(e)->get_constant();
}
const map<Expression, double>& get_expr_to_coeff_map_in_addition(
    const Expression& e) {
  return to_addition(e)->get_expr_to_coeff_map();
}
double get_constant_in_multiplication(const Expression& e) {
  return to_multiplication(e)->get_constant();
}
const map<Expression, Expression>& get_base_to_exponent_map_in_multiplication(
    const Expression& e) {
  return to_multiplication(e)->get_base_to_exponent_map();
}

const Formula& get_conditional_formula(const Expression& e) {
  return to_if_then_else(e)->get_conditional_formula();
}

const Expression& get_then_expression(const Expression& e) {
  return to_if_then_else(e)->get_then_expression();
}

const Expression& get_else_expression(const Expression& e) {
  return to_if_then_else(e)->get_else_expression();
}

const string& get_uninterpreted_function_name(const Expression& e) {
  return to_uninterpreted_function(e)->get_name();
}

Expression operator+(const Variable& var) { return Expression{var}; }
Expression operator-(const Variable& var) { return -Expression{var}; }

}  // namespace symbolic
}  // namespace drake
}  // namespace dreal
