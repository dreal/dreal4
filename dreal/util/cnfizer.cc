#include "dreal/util/cnfizer.h"

#include <algorithm>
#include <iostream>
#include <iterator>
#include <set>
#include <stdexcept>
#include <string>

namespace dreal {

using std::back_inserter;
using std::copy;
using std::cout;
using std::endl;
using std::runtime_error;
using std::set;
using std::shared_ptr;
using std::string;
using std::to_string;
using std::vector;

namespace {
// Forward declarations for the helper functions.
void Cnfize(const Variable& b, const Formula& f, vector<Formula>* clauses);
void CnfizeNegation(const Variable& b, const Formula& f,
                    vector<Formula>* clauses);
void CnfizeConjunction(const Variable& b, const Formula& f,
                       vector<Formula>* clauses);
void CnfizeDisjunction(const Variable& b, const Formula& f,
                       vector<Formula>* clauses);
}  // namespace

// The main function of the Cnfizer:
//  - It visits each node and introduce a Boolean variable `b` for
//    each subterm `f`, and keep the relation `b ⇔ f`.
//  - Then it cnfizes each `b ⇔ f` and make a conjunction of them.
vector<Formula> Cnfizer::Convert(const Formula& f) {
  map_.clear();
  vector<Formula> ret;
  const Formula head{Visit(f)};
  if (map_.empty()) {
    return {head};
  }
  for (auto const& p : map_) {
    if (get_variable(head).equal_to(p.first)) {
      if (is_conjunction(p.second)) {
        const set<Formula>& conjuncts(get_operands(p.second));
        copy(conjuncts.begin(), conjuncts.end(), back_inserter(ret));
      } else {
        ret.push_back(p.second);
      }
    } else {
      Cnfize(p.first, p.second, &ret);
    }
  }
  return ret;
}

Formula Cnfizer::Visit(const Formula& f) {
  // TODO(soonho): use cache.
  return VisitFormula<Formula>(this, f);
}

Formula Cnfizer::VisitFalse(const Formula& f) { return f; }
Formula Cnfizer::VisitTrue(const Formula& f) { return f; }
Formula Cnfizer::VisitVariable(const Formula& f) { return f; }
Formula Cnfizer::VisitEqualTo(const Formula& f) { return f; }
Formula Cnfizer::VisitNotEqualTo(const Formula& f) { return f; }
Formula Cnfizer::VisitGreaterThan(const Formula& f) { return f; }
Formula Cnfizer::VisitGreaterThanOrEqualTo(const Formula& f) { return f; }
Formula Cnfizer::VisitLessThan(const Formula& f) { return f; }
Formula Cnfizer::VisitLessThanOrEqualTo(const Formula& f) { return f; }
Formula Cnfizer::VisitForall(const Formula& f) { return f; }

Formula Cnfizer::VisitConjunction(const Formula& f) {
  // Introduce a new Boolean variable, `bvar` for `f` and record the
  // relation `bvar ⇔ f`.
  static size_t id{0};
  const set<Formula> transformed_operands{
      map(get_operands(f),
          [this](const Formula& formula) { return this->Visit(formula); })};
  const Variable bvar{string("conj") + to_string(id++),
                      Variable::Type::BOOLEAN};
  map_.emplace(bvar, make_conjunction(transformed_operands));
  return Formula{bvar};
}

Formula Cnfizer::VisitDisjunction(const Formula& f) {
  static size_t id{0};
  const set<Formula>& transformed_operands{
      map(get_operands(f),
          [this](const Formula& formula) { return this->Visit(formula); })};
  const Variable bvar{string("disj") + to_string(id++),
                      Variable::Type::BOOLEAN};
  map_.emplace(bvar, make_disjunction(transformed_operands));
  return Formula{bvar};
}

Formula Cnfizer::VisitNegation(const Formula& f) {
  const Formula& operand{get_operand(f)};
  if (is_atomic(operand)) {
    return f;
  } else {
    const Variable bvar{"neg", Variable::Type::BOOLEAN};
    const Formula transformed_operand{Visit(operand)};
    map_.emplace(bvar, !transformed_operand);
    return Formula{bvar};
  }
}

namespace {
// Cnfize b ⇔ f and add it to @p clauses. It calls Cnfize<FormulaKind> using
// pattern-matching.
void Cnfize(const Variable& b, const Formula& f, vector<Formula>* clauses) {
  switch (f.get_kind()) {
    case FormulaKind::False:
    case FormulaKind::True:
    case FormulaKind::Var:
    case FormulaKind::Eq:
    case FormulaKind::Neq:
    case FormulaKind::Gt:
    case FormulaKind::Geq:
    case FormulaKind::Lt:
    case FormulaKind::Leq:
    case FormulaKind::Forall:
    case FormulaKind::And:
      return CnfizeConjunction(b, f, clauses);
    case FormulaKind::Or:
      return CnfizeDisjunction(b, f, clauses);
    case FormulaKind::Not:
      return CnfizeNegation(b, f, clauses);
  }
  throw runtime_error{"Cnfize: Should be unreachable."};
}

// Add f to clauses if f is not true.
void Add(const Formula& f, vector<Formula>* clauses) {
  if (!is_true(f)) {
    clauses->push_back(f);
  }
}

// Add f₁ ⇔ f₂ to clauses.
void AddIff(const Formula& f1, const Formula& f2, vector<Formula>* clauses) {
  Add(imply(f1, f2), clauses);
  Add(imply(f2, f1), clauses);
}

// Cnfize b ⇔ ¬b₁ using the following equalities and add to clauses:
//   b ⇔ ¬b₁
// = (b → ¬b₁) ∧ (¬b₁ → b)
// = (¬b ∨ ¬b₁) ∧ (b₁ ∨ b)   (✓CNF)
void CnfizeNegation(const Variable& b, const Formula& f,
                    vector<Formula>* clauses) {
  AddIff(Formula{b}, f, clauses);
}  // namespace

// Cnfize b ⇔ (b₁ ∧ ... ∧ bₙ) using the following equalities and add
// to clauses:
//   b ⇔ (b₁ ∧ ... ∧ bₙ)
// = (b → (b₁ ∧ ... ∧ bₙ)) ∧ ((b₁ ∧ ... ∧ bₙ) → b)
// = (¬b ∨ (b₁ ∧ ... ∧ bₙ)) ∧ (¬b₁ ∨ ... ∨ ¬bₙ ∨ b)
// = (¬b ∨ b₁) ∧ ... (¬b ∨ bₙ) ∧ (¬b₁ ∨ ... ∨ ¬bₙ ∨ b)   (✓CNF)
void CnfizeConjunction(const Variable& b, const Formula& f,
                       vector<Formula>* clauses) {
  // operands = {b₁, ..., bₙ}
  const set<Formula>& operands{get_operands(f)};
  // negated_operands = {¬b₁, ..., ¬bₙ}
  const set<Formula>& negated_operands{
      map(operands, [](const Formula& formula) { return !formula; })};
  Formula ret{Formula::True()};
  for (const Formula b_i : operands) {
    Add(!b || b_i, clauses);
  }
  Add(make_disjunction(negated_operands) || b, clauses);
}

// Cnfize b ⇔ (b₁ ∨ ... ∨ bₙ) using the following equalities and add
// to clauses:
//   b ⇔ (b₁ ∨ ... ∨ bₙ)
// = (b → (b₁ ∨ ... ∨ bₙ)) ∧ ((b₁ ∨ ... ∨ bₙ) → b)
// = (¬b ∨ b₁ ∨ ... ∨ bₙ) ∧ ((¬b₁ ∧ ... ∧ ¬bₙ) ∨ b)
// = (¬b ∨ b₁ ∨ ... ∨ bₙ) ∧ (¬b₁ ∨ b) ∧ ... ∧ (¬bₙ ∨ b)   (✓CNF)
void CnfizeDisjunction(const Variable& b, const Formula& f,
                       vector<Formula>* clauses) {
  // negated_operands = {¬b₁, ..., ¬bₙ}
  const set<Formula>& negated_operands{
      map(get_operands(f), [](const Formula& formula) { return !formula; })};
  Add(!b || f, clauses);  // (¬b ∨ b₁ ∨ ... ∨ bₙ)
  for (const Formula neg_b_i : negated_operands) {
    Add(neg_b_i || b, clauses);
  }
}  // namespace
}  // namespace
}  // namespace dreal
