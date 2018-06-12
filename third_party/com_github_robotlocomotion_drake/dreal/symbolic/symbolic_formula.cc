#include "dreal/symbolic/symbolic_formula.h"

#include <cassert>
#include <cstddef>
#include <iostream>
#include <set>
#include <sstream>

#include "dreal/symbolic/symbolic_environment.h"
#include "dreal/symbolic/symbolic_expression.h"
#include "dreal/symbolic/symbolic_formula_cell.h"
#include "dreal/symbolic/symbolic_variable.h"
#include "dreal/symbolic/symbolic_variables.h"

namespace dreal {
namespace drake {
namespace symbolic {

using std::ostream;
using std::ostringstream;
using std::set;
using std::string;

bool operator<(FormulaKind k1, FormulaKind k2) {
  return static_cast<int>(k1) < static_cast<int>(k2);
}

Formula::Formula() : Formula{Formula::True().ptr_} {}

Formula::Formula(const Formula& f) {
  assert(f.ptr_ != nullptr);
  f.ptr_->increase_rc();
  ptr_ = f.ptr_;
}

Formula& Formula::operator=(const Formula& f) {
  assert(f.ptr_ != nullptr);
  f.ptr_->increase_rc();
  assert(ptr_ != nullptr);
  if (ptr_->decrease_rc() == 0) {
    delete ptr_;
  }
  ptr_ = f.ptr_;
  return *this;
}

Formula::Formula(Formula&& f) noexcept {
  assert(f.ptr_ != nullptr);
  ptr_ = f.ptr_;
  f.ptr_ = nullptr;
}

Formula& Formula::operator=(Formula&& f) noexcept {
  assert(ptr_ != nullptr);
  if (ptr_->decrease_rc() == 0) {
    delete ptr_;
  }
  assert(f.ptr_ != nullptr);
  ptr_ = f.ptr_;
  f.ptr_ = nullptr;
  return *this;
}

Formula::~Formula() {
  if (ptr_ && ptr_->decrease_rc() == 0) {
    delete ptr_;
  }
}

Formula::Formula(const FormulaCell* ptr) : ptr_{ptr} { ptr_->increase_rc(); }

Formula::Formula(const Variable& var) : Formula{new FormulaVar(var)} {}

FormulaKind Formula::get_kind() const {
  assert(ptr_ != nullptr);
  return ptr_->get_kind();
}

size_t Formula::get_hash() const {
  assert(ptr_ != nullptr);
  return ptr_->get_hash();
}

Variables Formula::GetFreeVariables() const {
  assert(ptr_ != nullptr);
  return ptr_->GetFreeVariables();
}

bool Formula::EqualTo(const Formula& f) const {
  assert(ptr_ != nullptr);
  assert(f.ptr_ != nullptr);
  if (ptr_ == f.ptr_) {
    // pointer equality
    return true;
  }
  if (get_kind() != f.get_kind()) {
    return false;
  }
  if (get_hash() != f.get_hash()) {
    return false;
  }
  // Same kind/hash, but it could be the result of hash collision,
  // check structural equality.
  return ptr_->EqualTo(*(f.ptr_));
}

bool Formula::Less(const Formula& f) const {
  const FormulaKind k1{get_kind()};
  const FormulaKind k2{f.get_kind()};
  if (k1 < k2) {
    return true;
  }
  if (k2 < k1) {
    return false;
  }
  return ptr_->Less(*(f.ptr_));
}

bool Formula::Evaluate(const Environment& env) const {
  assert(ptr_ != nullptr);
  return ptr_->Evaluate(env);
}

Formula Formula::Substitute(const Variable& var, const Expression& e) const {
  assert(ptr_ != nullptr);
  return ptr_->Substitute({{var, e}}, FormulaSubstitution{});
}

Formula Formula::Substitute(const Variable& var, const Formula& f) const {
  assert(ptr_ != nullptr);
  return ptr_->Substitute(ExpressionSubstitution{}, {{var, f}});
}

Formula Formula::Substitute(const ExpressionSubstitution& expr_subst,
                            const FormulaSubstitution& formula_subst) const {
  assert(ptr_ != nullptr);
  if (!expr_subst.empty() || !formula_subst.empty()) {
    return ptr_->Substitute(expr_subst, formula_subst);
  }
  return *this;
}

Formula Formula::Substitute(const ExpressionSubstitution& expr_subst) const {
  assert(ptr_ != nullptr);
  if (!expr_subst.empty()) {
    return ptr_->Substitute(expr_subst, FormulaSubstitution{});
  }
  return *this;
}

Formula Formula::Substitute(const FormulaSubstitution& formula_subst) const {
  assert(ptr_ != nullptr);
  if (!formula_subst.empty()) {
    return ptr_->Substitute(ExpressionSubstitution{}, formula_subst);
  }
  return *this;
}

string Formula::to_string() const {
  ostringstream oss;
  oss << *this;
  return oss.str();
}

Formula Formula::True() {
  static const Formula tt{new FormulaTrue()};
  return tt;
}

Formula Formula::False() {
  static const Formula ff{new FormulaFalse()};
  return ff;
}

Formula forall(const Variables& vars, const Formula& f) {
  return Formula{new FormulaForall(vars, f)};
}

Formula make_conjunction(const set<Formula>& formulas) {
  set<Formula> operands;
  for (const Formula& f : formulas) {
    if (is_false(f)) {
      // Short-circuits to False.
      // f₁ ∧ ... ∧ False ∧ ... ∧ fₙ => False
      return Formula::False();
    }
    if (is_true(f)) {
      // Drop redundant True.
      // f₁ ∧ ... ∧ True ∧ ... ∧ fₙ => f₁ ∧ ... ∧ fₙ
      continue;
    }
    if (is_conjunction(f)) {
      // Flattening.
      //    f₁ ∧ ... ∧ (fᵢ₁ ∧ ... ∧ fᵢₘ) ∧ ... ∧ fₙ
      // => f₁ ∧ ... ∧ fᵢ₁ ∧ ... ∧ fᵢₘ ∧ ... ∧ fₙ
      const auto& operands_in_f = get_operands(f);
      operands.insert(operands_in_f.cbegin(), operands_in_f.cend());
    } else {
      operands.insert(f);
    }
  }
  if (operands.empty()) {
    // ⋀{} = True
    return Formula::True();
  }
  if (operands.size() == 1) {
    return *(operands.begin());
  }
  // TODO(soonho-tri): Returns False if both f and ¬f appear in operands.
  return Formula{new FormulaAnd(operands)};
}

Formula operator&&(const Formula& f1, const Formula& f2) {
  return make_conjunction({f1, f2});
}

Formula operator&&(const Variable& v, const Formula& f) {
  return Formula(v) && f;
}
Formula operator&&(const Formula& f, const Variable& v) {
  return f && Formula(v);
}
Formula operator&&(const Variable& v1, const Variable& v2) {
  return Formula(v1) && Formula(v2);
}

Formula make_disjunction(const set<Formula>& formulas) {
  set<Formula> operands;
  for (const Formula& f : formulas) {
    if (is_true(f)) {
      // Short-circuits to True.
      // f₁ ∨ ... ∨ True ∨ ... ∨ fₙ => True
      return Formula::True();
    }
    if (is_false(f)) {
      // Drop redundant False.
      // f₁ ∨ ... ∨ False ∨ ... ∨ fₙ => f₁ ∨ ... ∨ fₙ
      continue;
    }
    if (is_disjunction(f)) {
      // Flattening.
      //    f₁ ∨ ... ∨ (fᵢ₁ ∨ ... ∨ fᵢₘ) ∨ ... ∨ fₙ
      // => f₁ ∨ ... ∨ fᵢ₁ ∨ ... ∨ fᵢₘ ∨ ... ∨ fₙ
      const auto& operands_in_f = get_operands(f);
      operands.insert(operands_in_f.cbegin(), operands_in_f.cend());
    } else {
      operands.insert(f);
    }
  }
  if (operands.empty()) {
    // ⋁{} = False
    return Formula::False();
  }
  if (operands.size() == 1) {
    return *(operands.begin());
  }
  // TODO(soonho-tri): Returns True if both f and ¬f appear in operands.
  return Formula{new FormulaOr(operands)};
}

Formula operator||(const Formula& f1, const Formula& f2) {
  return make_disjunction({f1, f2});
}
Formula operator||(const Variable& v, const Formula& f) {
  return Formula(v) || f;
}
Formula operator||(const Formula& f, const Variable& v) {
  return f || Formula(v);
}
Formula operator||(const Variable& v1, const Variable& v2) {
  return Formula(v1) || Formula(v2);
}

Formula operator!(const Formula& f) {
  if (f.EqualTo(Formula::True())) {
    return Formula::False();
  }
  if (f.EqualTo(Formula::False())) {
    return Formula::True();
  }
  // Simplification: ¬(¬f₁)  =>  f₁
  if (is_negation(f)) {
    return get_operand(f);
  }
  return Formula{new FormulaNot(f)};
}

Formula operator!(const Variable& v) { return !Formula(v); }

ostream& operator<<(ostream& os, const Formula& f) {
  assert(f.ptr_ != nullptr);
  return f.ptr_->Display(os);
}

Formula operator==(const Expression& e1, const Expression& e2) {
  // Simplification: E1 - E2 == 0  =>  True
  const Expression diff{e1 - e2};
  if (diff.get_kind() == ExpressionKind::Constant) {
    return diff.Evaluate() == 0.0 ? Formula::True() : Formula::False();
  }
  return Formula{new FormulaEq(e1, e2)};
}

Formula operator!=(const Expression& e1, const Expression& e2) {
  // Simplification: E1 - E2 != 0  =>  True
  const Expression diff{e1 - e2};
  if (diff.get_kind() == ExpressionKind::Constant) {
    return diff.Evaluate() != 0.0 ? Formula::True() : Formula::False();
  }
  return Formula{new FormulaNeq(e1, e2)};
}

Formula operator<(const Expression& e1, const Expression& e2) {
  // Simplification: E1 - E2 < 0  =>  True
  const Expression diff{e1 - e2};
  if (diff.get_kind() == ExpressionKind::Constant) {
    return diff.Evaluate() < 0 ? Formula::True() : Formula::False();
  }
  return Formula{new FormulaLt(e1, e2)};
}

Formula operator<=(const Expression& e1, const Expression& e2) {
  // Simplification: E1 - E2 <= 0  =>  True
  const Expression diff{e1 - e2};
  if (diff.get_kind() == ExpressionKind::Constant) {
    return diff.Evaluate() <= 0 ? Formula::True() : Formula::False();
  }
  return Formula{new FormulaLeq(e1, e2)};
}

Formula operator>(const Expression& e1, const Expression& e2) {
  // Simplification: E1 - E2 > 0  =>  True
  const Expression diff{e1 - e2};
  if (diff.get_kind() == ExpressionKind::Constant) {
    return diff.Evaluate() > 0 ? Formula::True() : Formula::False();
  }
  return Formula{new FormulaGt(e1, e2)};
}

Formula operator>=(const Expression& e1, const Expression& e2) {
  // Simplification: E1 - E2 >= 0  =>  True
  const Expression diff{e1 - e2};
  if (diff.get_kind() == ExpressionKind::Constant) {
    return diff.Evaluate() >= 0 ? Formula::True() : Formula::False();
  }
  return Formula{new FormulaGeq(e1, e2)};
}

bool is_false(const Formula& f) { return is_false(*f.ptr_); }
bool is_true(const Formula& f) { return is_true(*f.ptr_); }
bool is_variable(const Formula& f) { return is_variable(*f.ptr_); }
bool is_equal_to(const Formula& f) { return is_equal_to(*f.ptr_); }
bool is_not_equal_to(const Formula& f) { return is_not_equal_to(*f.ptr_); }
bool is_greater_than(const Formula& f) { return is_greater_than(*f.ptr_); }
bool is_greater_than_or_equal_to(const Formula& f) {
  return is_greater_than_or_equal_to(*f.ptr_);
}
bool is_less_than(const Formula& f) { return is_less_than(*f.ptr_); }
bool is_less_than_or_equal_to(const Formula& f) {
  return is_less_than_or_equal_to(*f.ptr_);
}
bool is_relational(const Formula& f) {
  return is_equal_to(f) || is_not_equal_to(f) || is_greater_than(f) ||
         is_greater_than_or_equal_to(f) || is_less_than(f) ||
         is_less_than_or_equal_to(f);
}
bool is_conjunction(const Formula& f) { return is_conjunction(*f.ptr_); }
bool is_disjunction(const Formula& f) { return is_disjunction(*f.ptr_); }
bool is_nary(const Formula& f) {
  return is_conjunction(f) || is_disjunction(f);
}
bool is_negation(const Formula& f) { return is_negation(*f.ptr_); }
bool is_forall(const Formula& f) { return is_forall(*f.ptr_); }

const Variable& get_variable(const Formula& f) {
  assert(is_variable(f));
  return to_variable(f)->get_variable();
}

const Expression& get_lhs_expression(const Formula& f) {
  assert(is_relational(f));
  return to_relational(f)->get_lhs_expression();
}
const Expression& get_rhs_expression(const Formula& f) {
  assert(is_relational(f));
  return to_relational(f)->get_rhs_expression();
}

const set<Formula>& get_operands(const Formula& f) {
  return to_nary(f)->get_operands();
}

const Formula& get_operand(const Formula& f) {
  return to_negation(f)->get_operand();
}

const Variables& get_quantified_variables(const Formula& f) {
  return to_forall(f)->get_quantified_variables();
}

const Formula& get_quantified_formula(const Formula& f) {
  return to_forall(f)->get_quantified_formula();
}

}  // namespace symbolic
}  // namespace drake
}  // namespace dreal