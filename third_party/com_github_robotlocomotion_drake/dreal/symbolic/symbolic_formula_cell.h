#pragma once

#include <atomic>
#include <functional>
#include <ostream>
#include <set>
#include <string>
#include <utility>

#include "dreal/symbolic/hash.h"
#include "dreal/symbolic/symbolic_environment.h"
#include "dreal/symbolic/symbolic_expression.h"
#include "dreal/symbolic/symbolic_formula.h"
#include "dreal/symbolic/symbolic_variable.h"
#include "dreal/symbolic/symbolic_variables.h"

namespace dreal {
namespace drake {
namespace symbolic {

/** Represents an abstract class which is the base of concrete symbolic-formula
 * classes (i.e. symbolic::FormulaAnd, symbolic::FormulaEq).
 *
 * \note It provides virtual function, FormulaCell::Display,
 * because operator<< is not allowed to be a virtual function.
 */
class FormulaCell {
 public:
  /** Default constructor (DELETED). */
  FormulaCell() = delete;

  /** Move-assign (DELETED). */
  FormulaCell& operator=(FormulaCell&& f) = delete;

  /** Copy-construct a formula from an lvalue. (DELETED) */
  FormulaCell(const FormulaCell& f) = delete;

  /** Move-construct a formula from an rvalue (DELETED). */
  FormulaCell(FormulaCell&& f) = delete;

  /** Copy-assign (DELETED). */
  FormulaCell& operator=(const FormulaCell& f) = delete;

  /** Returns kind of formula. */
  FormulaKind get_kind() const { return kind_; }
  /** Returns hash of formula. */
  size_t get_hash() const { return hash_; }
  /** Returns set of free variables in formula. */
  virtual Variables GetFreeVariables() const = 0;
  /** Checks structural equality. */
  virtual bool EqualTo(const FormulaCell& c) const = 0;
  /** Checks ordering. */
  virtual bool Less(const FormulaCell& c) const = 0;
  /** Evaluates under a given environment. */
  virtual bool Evaluate(const Environment& env) const = 0;
  /** Returns a Formula obtained by replacing all occurrences of the
   * variables in @p s in the current formula cell with the corresponding
   * expressions in @p s.
   */
  virtual Formula Substitute(const ExpressionSubstitution& expr_subst,
                             const FormulaSubstitution& formula_subst) = 0;
  /** Outputs string representation of formula into output stream @p os. */
  virtual std::ostream& Display(std::ostream& os) const = 0;

  /** Returns the reference count of this cell. */
  unsigned use_count() const { return rc_; }

 protected:
  /** Construct FormulaCell of kind @p k with @p hash. */
  FormulaCell(FormulaKind k, size_t hash);
  /** Default destructor. */
  virtual ~FormulaCell() = default;
  /** Returns a Formula pointing to this FormulaCell. */
  Formula GetFormula();

 private:
  const FormulaKind kind_{};
  const size_t hash_{};

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
  friend Formula;
};

/** Represents the base class for relational operators (==, !=, <, <=, >, >=).
 */
class RelationalFormulaCell : public FormulaCell {
 public:
  /** Default constructor (deleted). */
  RelationalFormulaCell() = delete;
  /** Default destructor (deleted). */
  ~RelationalFormulaCell() override = default;
  /** Move-construct a formula from an rvalue (DELETED). */
  RelationalFormulaCell(RelationalFormulaCell&& f) = delete;
  /** Copy-construct a formula from an lvalue (DELETED). */
  RelationalFormulaCell(const RelationalFormulaCell& f) = delete;
  /** Move-assign (DELETED). */
  RelationalFormulaCell& operator=(RelationalFormulaCell&& f) = delete;
  /** Copy-assign (DELETED). */
  RelationalFormulaCell& operator=(const RelationalFormulaCell& f) = delete;
  /** Construct RelationalFormulaCell of kind @p k with @p lhs and @p rhs. */
  RelationalFormulaCell(FormulaKind k, const Expression& lhs,
                        const Expression& rhs);
  Variables GetFreeVariables() const override;
  bool EqualTo(const FormulaCell& f) const override;
  bool Less(const FormulaCell& f) const override;

  /** Returns the expression on left-hand-side. */
  const Expression& get_lhs_expression() const { return e_lhs_; }
  /** Returns the expression on right-hand-side. */
  const Expression& get_rhs_expression() const { return e_rhs_; }

 private:
  const Expression e_lhs_;
  const Expression e_rhs_;
};

/** Represents the base class for N-ary logic operators (∧ and ∨).
 *
 * @note Internally this class maintains a set of symbolic formulas to avoid
 * duplicated elements (i.e. f1 ∧ ... ∧ f1).
 */
class NaryFormulaCell : public FormulaCell {
 public:
  /** Default constructor (deleted). */
  NaryFormulaCell() = delete;
  /** Default destructor (deleted). */
  ~NaryFormulaCell() override = default;
  /** Move-construct a formula from an rvalue (DELETED). */
  NaryFormulaCell(NaryFormulaCell&& f) = delete;
  /** Copy-construct a formula from an lvalue (DELETED). */
  NaryFormulaCell(const NaryFormulaCell& f) = delete;
  /** Move-assign (DELETED). */
  NaryFormulaCell& operator=(NaryFormulaCell&& f) = delete;
  /** Copy-assign (DELETED). */
  NaryFormulaCell& operator=(const NaryFormulaCell& f) = delete;
  /** Construct NaryFormulaCell of kind @p k with @p formulas. */
  NaryFormulaCell(FormulaKind k, std::set<Formula> formulas);
  Variables GetFreeVariables() const override;
  bool EqualTo(const FormulaCell& f) const override;
  bool Less(const FormulaCell& f) const override;
  /** Returns the formulas. */
  const std::set<Formula>& get_operands() const { return formulas_; }

  /** Returns the formulas. */
  std::set<Formula>& get_mutable_operands() { return formulas_; }

 protected:
  std::ostream& DisplayWithOp(std::ostream& os, const std::string& op) const;

 private:
  std::set<Formula> formulas_;
};

/** Symbolic formula representing true. */
class FormulaTrue : public FormulaCell {
 public:
  /** Default Constructor. */
  FormulaTrue();
  Variables GetFreeVariables() const override;
  bool EqualTo(const FormulaCell& f) const override;
  bool Less(const FormulaCell& f) const override;
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
};

/** Symbolic formula representing false. */
class FormulaFalse : public FormulaCell {
 public:
  /** Default Constructor. */
  FormulaFalse();
  Variables GetFreeVariables() const override;
  bool EqualTo(const FormulaCell& f) const override;
  bool Less(const FormulaCell& f) const override;
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
};

/** Symbolic formula representing a Boolean variable. */
class FormulaVar : public FormulaCell {
 public:
  /** Constructs a formula from @p var.
   * @pre @p var is of BOOLEAN type and not a dummy variable.
   */
  explicit FormulaVar(const Variable& v);
  Variables GetFreeVariables() const override;
  bool EqualTo(const FormulaCell& f) const override;
  bool Less(const FormulaCell& f) const override;
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_substubst) override;
  std::ostream& Display(std::ostream& os) const override;
  const Variable& get_variable() const;

 private:
  const Variable var_;
};

/** Symbolic formula representing equality (e1 = e2). */
class FormulaEq : public RelationalFormulaCell {
 public:
  /** Constructs from @p e1 and @p e2. */
  FormulaEq(const Expression& e1, const Expression& e2);
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
};

/** Symbolic formula representing disequality (e1 ≠ e2). */
class FormulaNeq : public RelationalFormulaCell {
 public:
  /** Constructs from @p e1 and @p e2. */
  FormulaNeq(const Expression& e1, const Expression& e2);
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
};

/** Symbolic formula representing 'greater-than' (e1 > e2). */
class FormulaGt : public RelationalFormulaCell {
 public:
  /** Constructs from @p e1 and @p e2. */
  FormulaGt(const Expression& e1, const Expression& e2);
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
};

/** Symbolic formula representing 'greater-than-or-equal-to' (e1 ≥ e2). */
class FormulaGeq : public RelationalFormulaCell {
 public:
  /** Constructs from @p e1 and @p e2. */
  FormulaGeq(const Expression& e1, const Expression& e2);
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
};

/** Symbolic formula representing 'less-than' (e1 < e2). */
class FormulaLt : public RelationalFormulaCell {
 public:
  /** Constructs from @p e1 and @p e2. */
  FormulaLt(const Expression& e1, const Expression& e2);
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
};

/** Symbolic formula representing 'less-than-or-equal-to' (e1 ≤ e2). */
class FormulaLeq : public RelationalFormulaCell {
 public:
  /** Constructs from @p e1 and @p e2. */
  FormulaLeq(const Expression& e1, const Expression& e2);
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
};

/** Symbolic formula representing conjunctions (f1 ∧ ... ∧ fn). */
class FormulaAnd : public NaryFormulaCell {
 public:
  /** Constructs from @p formulas. */
  explicit FormulaAnd(std::set<Formula> formulas);
  /** Constructs @p f1 ∧ @p f2. */
  FormulaAnd(const Formula& f1, const Formula& f2);
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
};

/** Symbolic formula representing disjunctions (f1 ∨ ... ∨ fn). */
class FormulaOr : public NaryFormulaCell {
 public:
  /** Constructs from @p formulas. */
  explicit FormulaOr(std::set<Formula> formulas);
  /** Constructs @p f1 ∨ @p f2. */
  FormulaOr(const Formula& f1, const Formula& f2);
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
};

/** Symbolic formula representing negations (¬f). */
class FormulaNot : public FormulaCell {
 public:
  /** Constructs from @p f. */
  explicit FormulaNot(const Formula& f);
  Variables GetFreeVariables() const override;
  bool EqualTo(const FormulaCell& f) const override;
  bool Less(const FormulaCell& f) const override;
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
  /** Returns the operand. */
  const Formula& get_operand() const { return f_; }

 private:
  const Formula f_;
};

/** Symbolic formula representing universal quantifications
 *  (∀ x₁, ..., * xn. F).
 */
class FormulaForall : public FormulaCell {
 public:
  /** Constructs from @p vars and @p f. */
  FormulaForall(const Variables& vars, const Formula& f);
  Variables GetFreeVariables() const override;
  bool EqualTo(const FormulaCell& f) const override;
  bool Less(const FormulaCell& f) const override;
  bool Evaluate(const Environment& env) const override;
  Formula Substitute(const ExpressionSubstitution& expr_subst,
                     const FormulaSubstitution& formula_subst) override;
  std::ostream& Display(std::ostream& os) const override;
  /** Returns the quantified variables. */
  const Variables& get_quantified_variables() const { return vars_; }
  /** Returns the quantified formula. */
  const Formula& get_quantified_formula() const { return f_; }

 private:
  const Variables vars_;  // Quantified variables.
  const Formula f_;       // Quantified formula.
};

/** Checks if @p f is structurally equal to False formula. */
bool is_false(const FormulaCell& f);
/** Checks if @p f is structurally equal to True formula. */
bool is_true(const FormulaCell& f);
/** Checks if @p f is a variable formula. */
bool is_variable(const FormulaCell& f);
/** Checks if @p f is a formula representing equality (==). */
bool is_equal_to(const FormulaCell& f);
/** Checks if @p f is a formula representing disequality (!=). */
bool is_not_equal_to(const FormulaCell& f);
/** Checks if @p f is a formula representing greater-than (>). */
bool is_greater_than(const FormulaCell& f);
/** Checks if @p f is a formula representing greater-than-or-equal-to (>=). */
bool is_greater_than_or_equal_to(const FormulaCell& f);
/** Checks if @p f is a formula representing less-than (<). */
bool is_less_than(const FormulaCell& f);
/** Checks if @p f is a formula representing less-than-or-equal-to (<=). */
bool is_less_than_or_equal_to(const FormulaCell& f);
/** Checks if @p f is a relational formula ({==, !=, >, >=, <, <=}). */
bool is_relational(const FormulaCell& f);
/** Checks if @p f is a conjunction (∧). */
bool is_conjunction(const FormulaCell& f);
/** Checks if @p f is a disjunction (∨). */
bool is_disjunction(const FormulaCell& f);
/** Checks if @p f is a negation (¬). */
bool is_negation(const FormulaCell& f);
/** Checks if @p f is a Forall formula (∀). */
bool is_forall(const FormulaCell& f);

/** Casts @p f_ptr to @c const FormulaFalse*.
 * @pre @c is_false(*f_ptr) is true.
 */
const FormulaFalse* to_false(const FormulaCell* f_ptr);
/** Casts @p f to @c const FormulaFalse*.
 * @pre @c is_false(f) is true.
 */
const FormulaFalse* to_false(const Formula& f);

/** Casts @p f_ptr to @c const FormulaTrue*.
 * @pre @c is_true(*f_ptr) is true.
 */
const FormulaTrue* to_true(const FormulaCell* f_ptr);
/** Casts @p f to @c const FormulaTrue*.
 * @pre @c is_true(f) is true.
 */
const FormulaTrue* to_true(const Formula& f);

/** Casts @p f_ptr to @c const FormulaVar*.
 * @pre @c is_variable(*f_ptr) is true.
 */
const FormulaVar* to_variable(const FormulaCell* f_ptr);
/** Casts @p f to @c const FormulaVar*.
 * @pre @c is_variable(f) is true.
 */
const FormulaVar* to_variable(const Formula& f);

/** Casts @p f_ptr to @c const RelationalFormulaCell*.
 * @pre @c is_relational(*f_ptr) is true.
 */
const RelationalFormulaCell* to_relational(const FormulaCell* f_ptr);

/** Casts @p f to @c const RelationalFormulaCell*.
 * @pre @c is_relational(f) is true.
 */
const RelationalFormulaCell* to_relational(const Formula& f);

/** Casts @p f_ptr to @c const FormulaEq*.
 * @pre @c is_equal_to(*f_ptr) is true.
 */
const FormulaEq* to_equal_to(const FormulaCell* f_ptr);

/** Casts @p f to @c const FormulaEq*.
 * @pre @c is_equal_to(f) is true.
 */
const FormulaEq* to_equal_to(const Formula& f);

/** Casts @p f_ptr to @c const FormulaNeq*.
 * @pre @c is_not_equal_to(*f_ptr) is true.
 */
const FormulaNeq* to_not_equal_to(const FormulaCell* f_ptr);

/** Casts @p f to @c const FormulaNeq*.
 * @pre @c is_not_equal_to(f) is true.
 */
const FormulaNeq* to_not_equal_to(const Formula& f);

/** Casts @p f_ptr to @c const FormulaGt*.
 * @pre @c is_greater_than(*f_ptr) is true.
 */
const FormulaGt* to_greater_than(const FormulaCell* f_ptr);

/** Casts @p f to @c const FormulaGt*.
 * @pre @c is_greater_than(f) is true.
 */
const FormulaGt* to_greater_than(const Formula& f);

/** Casts @p f_ptr to @c const FormulaGeq*.
 * @pre @c is_greater_than_or_equal_to(*f_ptr) is true.
 */
const FormulaGeq* to_greater_than_or_equal_to(const FormulaCell* f_ptr);

/** Casts @p f to @c const FormulaGeq*.
 * @pre @c is_greater_than_or_equal_to(f) is true.
 */
const FormulaGeq* to_greater_than_or_equal_to(const Formula& f);

/** Casts @p f_ptr to @c const FormulaLt*.
 * @pre @c is_less_than(*f_ptr) is true.
 */
const FormulaLt* to_less_than(const FormulaCell* f_ptr);

/** Casts @p f to @c const FormulaLt*.
 * @pre @c is_less_than(f) is true.
 */
const FormulaLt* to_less_than(const Formula& f);

/** Casts @p f_ptr to @c const FormulaLeq*.
 * @pre @c is_less_than_or_equal_to(*f_ptr) is true.
 */
const FormulaLeq* to_less_than_or_equal_to(const FormulaCell* f_ptr);

/** Casts @p f to @c const FormulaLeq*.
 * @pre @c is_less_than_or_equal_to(f) is true.
 */
const FormulaLeq* to_less_than_or_equal_to(const Formula& f);

/** Casts @p f_ptr to @c const FormulaAnd*.
 * @pre @c is_conjunction(*f_ptr) is true.
 */
const FormulaAnd* to_conjunction(const FormulaCell* f_ptr);

/** Casts @p f to @c const FormulaAnd*.
 * @pre @c is_conjunction(f) is true.
 */
const FormulaAnd* to_conjunction(const Formula& f);

/** Casts @p f_ptr to @c const FormulaOr*.
 * @pre @c is_disjunction(*f_ptr) is true.
 */
const FormulaOr* to_disjunction(const FormulaCell* f_ptr);

/** Casts @p f to @c const FormulaOr*.
 * @pre @c is_disjunction(f) is true.
 */
const FormulaOr* to_disjunction(const Formula& f);

/** Casts @p f_ptr to @c const NaryFormulaCell*.
 * @pre @c is_nary(*f_ptr) is true.
 */
const NaryFormulaCell* to_nary(const FormulaCell* f_ptr);

/** Casts @p f to @c const NaryFormulaCell*.
 * @pre @c is_nary(f) is true.
 */
const NaryFormulaCell* to_nary(const Formula& f);

/** Casts @p f_ptr to `NaryFormulaCell*`.
 * @pre `is_nary(*f_ptr)` is true.
 */
NaryFormulaCell* to_nary(FormulaCell* f_ptr);

/** Casts @p f to `NaryFormulaCell*`.
 * @pre `is_nary(f)` is true.
 */
NaryFormulaCell* to_nary(Formula& f);

/** Casts @p f_ptr to @c const FormulaNot*.
 *  @pre @c is_negation(*f_ptr) is true.
 */
const FormulaNot* to_negation(const FormulaCell* f_ptr);

/** Casts @p f to @c const FormulaNot*.
 *  @pre @c is_negation(f) is true.
 */
const FormulaNot* to_negation(const Formula& f);

/** Casts @p f_ptr to @c const FormulaForall*.
 *  @pre @c is_forall(*f_ptr) is true.
 */
const FormulaForall* to_forall(const FormulaCell* f_ptr);

/** Casts @p f to @c const FormulaForall*.
 *  @pre @c is_forall(f) is true.
 */
const FormulaForall* to_forall(const Formula& f);

}  // namespace symbolic
}  // namespace drake
}  // namespace dreal
