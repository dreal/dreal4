#pragma once

#include <functional>
#include <ostream>
#include <set>
#include <string>
#include <utility>

#include "dreal/symbolic/hash.h"
#include "dreal/symbolic/symbolic_environment.h"
#include "dreal/symbolic/symbolic_expression.h"
#include "dreal/symbolic/symbolic_variable.h"
#include "dreal/symbolic/symbolic_variables.h"

namespace dreal {
namespace drake {
namespace symbolic {

/** Kinds of symbolic formulas. */
enum class FormulaKind {
  False,   ///< ⊥
  True,    ///< ⊤
  Var,     ///< Boolean Variable
  Eq,      ///< =
  Neq,     ///< !=
  Gt,      ///< >
  Geq,     ///< >=
  Lt,      ///< <
  Leq,     ///< <=
  And,     ///< Conjunction (∧)
  Or,      ///< Disjunction (∨)
  Not,     ///< Negation (¬)
  Forall,  ///< Universal quantification (∀)
};

// Total ordering between FormulaKinds
bool operator<(FormulaKind k1, FormulaKind k2);

class FormulaCell;            // In symbolic/symbolic_formula_cell.h
class FormulaFalse;           // In symbolic/symbolic_formula_cell.h
class FormulaTrue;            // In symbolic/symbolic_formula_cell.h
class FormulaVar;             // In symbolic/symbolic_formula_cell.h
class RelationalFormulaCell;  // In symbolic/symbolic_formula_cell.h
class FormulaEq;              // In symbolic/symbolic_formula_cell.h
class FormulaNeq;             // In symbolic/symbolic_formula_cell.h
class FormulaGt;              // In symbolic/symbolic_formula_cell.h
class FormulaGeq;             // In symbolic/symbolic_formula_cell.h
class FormulaLt;              // In symbolic/symbolic_formula_cell.h
class FormulaLeq;             // In symbolic/symbolic_formula_cell.h
class NaryFormulaCell;        // In symbolic/symbolic_formula_cell.h
class FormulaNot;             // In symbolic/symbolic_formula_cell.h
class FormulaAnd;             // In symbolic/symbolic_formula_cell.h
class FormulaOr;              // In symbolic/symbolic_formula_cell.h
class FormulaForall;          // In symbolic/symbolic_formula_cell.h

/** Represents a symbolic form of a first-order logic formula.

It has the following grammar:

\verbatim
    F := ⊥ | ⊤ | Var | E = E | E ≠ E | E > E | E ≥ E | E < E | E ≤ E
       | E ∧ ... ∧ E | E ∨ ... ∨ E | ¬F | ∀ x₁, ..., xn. F
\endverbatim

In the implementation, Formula is a simple wrapper including a raw
pointer to FormulaCell class which is a super-class of different kinds
of symbolic formulas (i.e. FormulaAnd, FormulaOr, FormulaEq).

\note The sharing of sub-expressions is not yet implemented.

The following simple simplifications are implemented:
\verbatim
    E1 = E2        ->  True    (if E1 and E2 are structurally equal)
    E1 ≠ E2        ->  False   (if E1 and E2 are structurally equal)
    E1 > E2        ->  False   (if E1 and E2 are structurally equal)
    E1 ≥ E2        ->  True    (if E1 and E2 are structurally equal)
    E1 < E2        ->  False   (if E1 and E2 are structurally equal)
    E1 ≤ E2        ->  True    (if E1 and E2 are structurally equal)
    F1 ∧ F2        ->  False   (if either F1 or F2 is False)
    F1 ∨ F2        ->  True    (if either F1 or F2 is True)
    ¬(¬(F))        ->  F
\endverbatim

We flatten nested conjunctions (or disjunctions) at the construction. A
conjunction (resp. disjunction) takes a set of conjuncts (resp. disjuncts). Note
that any duplicated conjunct/disjunct is removed. For example, both of `f1 &&
(f2 && f1)` and `(f1 && f2) && f1` are flattened to `f1 && f2 && f1` and
simplified into `f1 && f2`. As a result, the two are identified as the same
formula.

\note Formula class has an explicit conversion operator to bool. It evaluates a
symbolic formula under an empty environment. If a symbolic formula includes
variables, the conversion operator throws an exception. This operator is only
intended for third-party code doing things like `(imag(SymbolicExpression(0))
== SymbolicExpression(0)) { ... };` that we found in Eigen3 codebase. In
general, a user of this class should explicitly call `Evaluate` from within
Drake for readability.

*/
class Formula {
 public:
  /** Default constructor. */
  Formula();
  Formula(const Formula&);
  Formula& operator=(const Formula&);
  Formula(Formula&&) noexcept;
  Formula& operator=(Formula&&) noexcept;
  ~Formula();

  explicit Formula(FormulaCell* ptr);

  /** Constructs a formula from @p var.
   * @pre @p var is of BOOLEAN type and not a dummy variable.
   */
  explicit Formula(const Variable& var);

  FormulaKind get_kind() const;
  size_t get_hash() const;

  /** Gets free variables (unquantified variables).
   *
   * @note For the first call, it traverses every node in the formula tree and
   * caches the result. The following calls are done in O(1) time.
   */
  const Variables& GetFreeVariables() const;

  /** Checks structural equality*/
  bool EqualTo(const Formula& f) const;

  /** Checks lexicographical ordering between this and @p e.
   *
   * If the two formulas f1 and f2 have different kinds k1 and k2 respectively,
   * f1.Less(f2) is equal to k1 < k2. If f1 and f2 are expressions of the same
   * kind, we check the ordering between f1 and f2 by comparing their elements
   * lexicographically.
   *
   * For example, in case of And, let f1 and f2 be
   *
   *     f1 = f_1,1 ∧ ... ∧ f_1,n
   *     f2 = f_2,1 ∧ ... ∧ f_2,m
   *
   * f1.Less(f2) is true if there exists an index i (<= n, m) such that
   * for all j < i, we have
   *
   *     ¬(f_1_j.Less(f_2_j)) ∧ ¬(f_2_j.Less(f_1_j))
   *
   * and f_1_i.Less(f_2_i) holds.
   *
   * This function is used as a compare function in
   * std::map<symbolic::Formula> and std::set<symbolic::Formula> via
   * std::less<symbolic::Formula>. */
  bool Less(const Formula& f) const;

  /** Evaluates under a given environment (by default, an empty environment).
   *
   * @throws runtime_error if a variable `v` is needed for an evaluation but not
   * provided by @p env.
   *
   * Note that for an equality e₁ = e₂ and an inequality e₁ ≠ e₂, this method
   * partially evaluates e₁ and e₂ and checks the structural equality of the two
   * results if @p env does not provide complete information to call Evaluate on
   * e₁ and e₂.
   */
  bool Evaluate(const Environment& env = Environment{}) const;

  /** Returns a copy of this formula replacing all occurrences of @p var
   * with @p e.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Formula Substitute(const Variable& var, const Expression& e) const;

  /** Returns a copy of this formula replacing all occurrences of @p var
   * with @p f.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Formula Substitute(const Variable& var, const Formula& f) const;

  /** Returns a copy of this formula replacing all occurrences of the variables
   * in @p expr_subst with corresponding expressions in @p expr_subst and all
   * occurrences of the variables in @p formula_subst with corresponding
   * formulas in @p formula_subst.
   *
   * Note that the substitutions occur simultaneously. For example, (x / y >
   * 0).Substitute({{x, y}, {y, x}}, {}) gets (y / x > 0).
   *
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) const;

  /** Returns a copy of this formula replacing all occurrences of the variables
   * in @p expr_subst with corresponding expressions in @p expr_subst.
   *
   * @note This is equivalent to `Substitute(expr_subst, {})`.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Formula Substitute(const ExpressionSubstitution& expr_subst) const;

  /** Returns a copy of this formula replacing all
   * occurrences of the variables in @p formula_subst with corresponding
   * formulas in @p formula_subst.
   *
   * @note This is equivalent to `Substitute({}, formula_subst)`.
   * @throws std::runtime_error if NaN is detected during substitution.
   */
  Formula Substitute(const FormulaSubstitution& formula_subst) const;

  /** Returns string representation of Formula. */
  std::string to_string() const;

  static Formula True();
  static Formula False();

  /** Conversion to bool. */
  explicit operator bool() const { return Evaluate(); }

  friend std::ostream& operator<<(std::ostream& os, const Formula& f);
  friend void swap(Formula& a, Formula& b) { std::swap(a.ptr_, b.ptr_); }

  friend bool is_false(const Formula& f);
  friend bool is_true(const Formula& f);
  friend bool is_variable(const Formula& f);
  friend bool is_equal_to(const Formula& f);
  friend bool is_not_equal_to(const Formula& f);
  friend bool is_greater_than(const Formula& f);
  friend bool is_greater_than_or_equal_to(const Formula& f);
  friend bool is_less_than(const Formula& f);
  friend bool is_less_than_or_equal_to(const Formula& f);
  friend bool is_relational(const Formula& f);
  friend bool is_conjunction(const Formula& f);
  friend bool is_disjunction(const Formula& f);
  friend bool is_negation(const Formula& f);
  friend bool is_forall(const Formula& f);

  // Note that the following cast functions are only for low-level operations
  // and not exposed to the user of symbolic_formula.h. These functions are
  // declared in symbolic_formula_cell.h header.
  friend const FormulaFalse* to_false(const Formula& f);
  friend const FormulaTrue* to_true(const Formula& f);
  friend const FormulaVar* to_variable(const Formula& f);
  friend const RelationalFormulaCell* to_relational(const Formula& f);
  friend const FormulaEq* to_equal_to(const Formula& f);
  friend const FormulaNeq* to_not_equal_to(const Formula& f);
  friend const FormulaGt* to_greater_than(const Formula& f);
  friend const FormulaGeq* to_greater_than_or_equal_to(const Formula& f);
  friend const FormulaLt* to_less_than(const Formula& f);
  friend const FormulaLeq* to_less_than_or_equal_to(const Formula& f);
  friend const NaryFormulaCell* to_nary(const Formula& f);
  friend NaryFormulaCell* to_nary(Formula& f);
  friend const FormulaAnd* to_conjunction(const Formula& f);
  friend const FormulaOr* to_disjunction(const Formula& f);
  friend const FormulaNot* to_negation(const Formula& f);
  friend const FormulaForall* to_forall(const Formula& f);

  // Returns f1 = f1 && f2.
  static Formula make_conjunction(Formula& f1, const Formula& f2);
  // Returns f1 = f1 || f2.
  static Formula make_disjunction(Formula& f1, const Formula& f2);

  friend FormulaCell;

 private:
  FormulaCell* ptr_;

  // Storage to cache the result of GetFreevariables().
  mutable std::shared_ptr<Variables> free_variables_;
};

/** Returns a formula @p f, universally quantified by variables @p vars. */
Formula forall(const Variables& vars, const Formula& f);

/** Returns a conjunction of @p formulas. It performs the following
 * simplification:
 *
 * - make_conjunction({}) returns True.
 * - make_conjunction({f₁}) returns f₁.
 * - If False ∈ @p formulas, it returns False.
 * - If True ∈ @p formulas, it will not appear in the return value.
 * - Nested conjunctions will be flattened. For example, make_conjunction({f₁,
 *   f₂ ∧ f₃}) returns f₁ ∧ f₂ ∧ f₃.
 */
Formula make_conjunction(const std::set<Formula>& formulas);
Formula operator&&(const Formula& f1, const Formula& f2);
Formula operator&&(const Formula& f1, Formula&& f2);
Formula operator&&(Formula&& f1, const Formula& f2);
Formula operator&&(Formula&& f1, Formula&& f2);

Formula operator&&(const Variable& v, const Formula& f);
Formula operator&&(const Variable& v, Formula&& f);
Formula operator&&(const Formula& f, const Variable& v);
Formula operator&&(Formula&& f, const Variable& v);
Formula operator&&(const Variable& v1, const Variable& v2);

/** Returns a disjunction of @p formulas. It performs the following
 * simplification:
 *
 * - make_disjunction({}) returns False.
 * - make_disjunction({f₁}) returns f₁.
 * - If True ∈ @p formulas, it returns True.
 * - If False ∈ @p formulas, it will not appear in the return value.
 * - Nested disjunctions will be flattened. For example, make_disjunction({f₁,
 *   f₂ ∨ f₃}) returns f₁ ∨ f₂ ∨ f₃.
 */
Formula make_disjunction(const std::set<Formula>& formulas);
Formula operator||(const Formula& f1, const Formula& f2);
Formula operator||(const Formula& f1, Formula&& f2);
Formula operator||(Formula&& f1, const Formula& f2);
Formula operator||(Formula&& f1, Formula&& f2);

Formula operator||(const Variable& v, const Formula& f);
Formula operator||(const Variable& v, Formula&& f);
Formula operator||(const Formula& f, const Variable& v);
Formula operator||(Formula&& f, const Variable& v);
Formula operator||(const Variable& v1, const Variable& v2);

Formula operator!(const Formula& f);
Formula operator!(const Variable& v);

/** Returns a formula representing v1 and v2 are equivalent.
 * - When v1 and v2 are scalar variables (of type
 *   CONTINUOUS/BINARY/INTEGER), it forms `v1 == v2`.
 * - When v1 and v2 are boolean variables, it returns `v1 ↔ v2`.
 */
Formula operator==(const Variable& v1, const Variable& v2);

/** Returns a formula representing (e1 = e2). */
Formula operator==(const Expression& e1, const Expression& e2);

/** Returns a formula representing f1 ↔ f2. */
Formula operator==(const Formula& f1, const Formula& f2);

/** Returns a formula representing v ↔ f. */
Formula operator==(const Variable& v, const Formula& f);

/** Returns a formula representing f ↔ v. */
Formula operator==(const Formula& f, const Variable& v);

/** Returns a formula representing v1 and v2 are *not* equivalent.
 * - When v1 and v2 are scalar variables (of type
 *   CONTINUOUS/BINARY/INTEGER), it forms `v1 ≠ v2`.
 * - When v1 and v2 are boolean variables, it returns `¬(v1 ↔ v2)`.
 */
Formula operator!=(const Variable& v1, const Variable& v2);

/** Returns a formula representing e1 ≠ e2. */
Formula operator!=(const Expression& e1, const Expression& e2);

/** Returns a formula representing ¬(f1 ↔ f2). */
Formula operator!=(const Formula& f1, const Formula& f2);

/** Returns a formula representing ¬(v ↔ f). */
Formula operator!=(const Variable& v, const Formula& f);

/** Returns a formula representing ¬(f ↔ v). */
Formula operator!=(const Formula& f, const Variable& v);

Formula operator<(const Expression& e1, const Expression& e2);
Formula operator<=(const Expression& e1, const Expression& e2);
Formula operator>(const Expression& e1, const Expression& e2);
Formula operator>=(const Expression& e1, const Expression& e2);

std::ostream& operator<<(std::ostream& os, const Formula& f);

/** Checks if @p f is structurally equal to False formula. */
bool is_false(const Formula& f);
/** Checks if @p f is structurally equal to True formula. */
bool is_true(const Formula& f);
/** Checks if @p f is a variable formula. */
bool is_variable(const Formula& f);
/** Checks if @p f is a formula representing equality (==). */
bool is_equal_to(const Formula& f);
/** Checks if @p f is a formula representing disequality (!=). */
bool is_not_equal_to(const Formula& f);
/** Checks if @p f is a formula representing greater-than (>). */
bool is_greater_than(const Formula& f);
/** Checks if @p f is a formula representing greater-than-or-equal-to (>=). */
bool is_greater_than_or_equal_to(const Formula& f);
/** Checks if @p f is a formula representing less-than (<). */
bool is_less_than(const Formula& f);
/** Checks if @p f is a formula representing less-than-or-equal-to (<=). */
bool is_less_than_or_equal_to(const Formula& f);
/** Checks if @p f is a relational formula ({==, !=, >, >=, <, <=}). */
bool is_relational(const Formula& f);
/** Checks if @p f is a conjunction (∧). */
bool is_conjunction(const Formula& f);
/** Checks if @p f is a disjunction (∨). */
bool is_disjunction(const Formula& f);
/** Checks if @p f is a n-ary formula ({∧, ∨}). */
bool is_nary(const Formula& f);
/** Checks if @p f is a negation (¬). */
bool is_negation(const Formula& f);
/** Checks if @p f is a Forall formula (∀). */
bool is_forall(const Formula& f);

/** Returns the embedded variable in the variable formula @p f.
 *  @pre @p f is a variable formula.
 */
const Variable& get_variable(const Formula& f);

/** Returns the lhs-argument of a relational formula @p f.
 *  @pre @p f is a relational formula.
 */
const Expression& get_lhs_expression(const Formula& f);

/** Returns the rhs-argument of a relational formula @p f.
 *  @pre @p f is a relational formula.
 */
const Expression& get_rhs_expression(const Formula& f);

/** Returns the set of formulas in a n-ary formula @p f.
 *  @pre @p f is a n-ary formula.
 */
const std::set<Formula>& get_operands(const Formula& f);

/** Returns the formula in a negation formula @p f.
 *  @pre @p f is a negation formula.
 */
const Formula& get_operand(const Formula& f);

/** Returns the quantified variables in a forall formula @p f.
 *  @pre @p f is a forall formula.
 */
const Variables& get_quantified_variables(const Formula& f);

/** Returns the quantified formula in a forall formula @p f.
 *  @pre @p f is a forall formula.
 */
const Formula& get_quantified_formula(const Formula& f);

namespace detail {
/// Returns @p f1 ∧ @p f2. We have it because gcc-4.8 does not have
/// `std::logical_and`.
inline Formula logic_and(const Formula& f1, const Formula& f2) {
  return f1 && f2;
}
}  // namespace detail
}  // namespace symbolic

/** Computes the hash value of a symbolic formula. */
template <>
struct hash_value<symbolic::Formula> {
  size_t operator()(const symbolic::Formula& f) const { return f.get_hash(); }
};
}  // namespace drake
}  // namespace dreal

namespace std {
/* Provides std::less<dreal::drake::symbolic::Formula>. */
template <>
struct less<dreal::drake::symbolic::Formula> {
  bool operator()(const dreal::drake::symbolic::Formula& lhs,
                  const dreal::drake::symbolic::Formula& rhs) const {
    return lhs.Less(rhs);
  }
};

/* Provides std::equal_to<dreal::drake::symbolic::Formula>. */
template <>
struct equal_to<dreal::drake::symbolic::Formula> {
  bool operator()(const dreal::drake::symbolic::Formula& lhs,
                  const dreal::drake::symbolic::Formula& rhs) const {
    return lhs.EqualTo(rhs);
  }
};

template <>
struct hash<dreal::drake::symbolic::Formula> {
  size_t operator()(const dreal::drake::symbolic::Formula& f) const {
    return f.get_hash();
  }
};

}  // namespace std
