#include "dreal/util/symbolic.h"

#include <algorithm>
#include <iterator>
#include <stdexcept>

namespace dreal {

using std::function;
using std::inserter;
using std::runtime_error;
using std::set;
using std::transform;

Formula imply(const Formula& f1, const Formula& f2) { return !f1 || f2; }

Formula iff(const Formula& f1, const Formula& f2) {
  return imply(f1, f2) && imply(f2, f1);
}

set<Formula> map(const set<Formula>& formulas,
                 const function<Formula(const Formula&)>& func) {
  set<Formula> result;
  transform(formulas.cbegin(), formulas.cend(),
            inserter(result, result.begin()), func);
  return result;
}

bool is_atomic(const Formula& f) {
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
      return true;
    case FormulaKind::And:
    case FormulaKind::Or:
      return false;
    case FormulaKind::Not:
      return is_variable(get_operand(f));
  }
  throw runtime_error{"Should be unreachable."};
}

bool is_clause(const Formula& f) {
  if (is_atomic(f)) {
    return true;
  }
  if (is_negation(f)) {
    return is_atomic(get_operand(f));
  }
  if (is_conjunction(f)) {
    return false;
  }
  if (is_disjunction(f)) {
    const auto& operands = get_operands(f);
    const bool result{
        all_of(operands.cbegin(), operands.cend(),
               [](const Formula& formula) { return is_atomic(formula); })};
    return result;
  }
  throw runtime_error{"Should be unreachable."};
}

bool is_cnf(const Formula& f) {
  if (is_atomic(f)) {
    return true;
  }
  if (is_disjunction(f)) {
    return is_clause(f);
  }
  if (is_conjunction(f)) {
    const auto& operands = get_operands(f);
    const bool result{
        all_of(operands.cbegin(), operands.cend(),
               [](const Formula& formula) { return is_clause(formula); })};
    return result;
  }
  throw runtime_error{"Should be unreachable."};
}

namespace {
/// Visitor class which strengthens a formula by delta.
class DeltaStrengthenVisitor {
 public:
  DeltaStrengthenVisitor() = default;
  Formula Strengthen(const Formula& f, const double delta) const {
    if (delta == 0) {
      return f;
    }
    return Visit(f, delta);
  }

 private:
  Formula Visit(const Formula& f, const double delta) const {
    return VisitFormula<Formula>(this, f, delta);
  }
  Formula VisitFalse(const Formula& f, const double) const { return f; }
  Formula VisitTrue(const Formula& f, const double) const { return f; }
  Formula VisitVariable(const Formula& f, const double) const { return f; }
  Formula VisitEqualTo(const Formula& f, const double delta) const {
    if (delta > 0) {
      return Formula::False();
    } else {
      //     lhs = rhs
      // -> (lhs >= rhs) ∧ (lhs <= rhs)
      // -> (lhs - rhs >= 0) ∧ (0 <= rhs - lhs)
      //
      // After weakening (note that delta is negative), we have:
      // -> (lhs - rhs >= delta) ∧ (delta <= rhs - lhs)

      const Expression& lhs{get_lhs_expression(f)};
      const Expression& rhs{get_rhs_expression(f)};
      return (lhs - rhs >= delta) && (delta <= rhs - lhs);
    }
  }
  Formula VisitNotEqualTo(const Formula& f, const double delta) const {
    if (delta > 0) {
      //     lhs ≠ rhs
      // -> (lhs > rhs) ∨ (lhs < rhs)
      // -> (lhs - rhs > 0) ∨ (0 < rhs - lhs)
      //
      // After strengthening, we have:
      //     (lhs - rhs > delta) ∨ (delta < rhs - lhs)
      const Expression& lhs{get_lhs_expression(f)};
      const Expression& rhs{get_rhs_expression(f)};
      return (lhs - rhs > delta) || (delta < rhs - lhs);
    } else {
      return Formula::True();
    }
  }
  Formula VisitGreaterThan(const Formula& f, const double delta) const {
    //     lhs > rhs
    //
    // After strengthening, we have:
    //     (lhs - rhs > delta)
    const Expression& lhs{get_lhs_expression(f)};
    const Expression& rhs{get_rhs_expression(f)};
    return (lhs - rhs > delta);
  }
  Formula VisitGreaterThanOrEqualTo(const Formula& f,
                                    const double delta) const {
    //     lhs >= rhs
    //
    // After strengthening, we have:
    //     (lhs - rhs >= delta)
    const Expression& lhs{get_lhs_expression(f)};
    const Expression& rhs{get_rhs_expression(f)};
    return (lhs - rhs >= delta);
  }
  Formula VisitLessThan(const Formula& f, const double delta) const {
    //     lhs < rhs
    //
    // After strengthening, we have:
    //     (delta < rhs - lhs)
    const Expression& lhs{get_lhs_expression(f)};
    const Expression& rhs{get_rhs_expression(f)};
    return (delta < rhs - lhs);
  }
  Formula VisitLessThanOrEqualTo(const Formula& f, const double delta) const {
    //     lhs <= rhs
    //
    // After strengthening, we have:
    //     (delta <= rhs - lhs)
    const Expression& lhs{get_lhs_expression(f)};
    const Expression& rhs{get_rhs_expression(f)};
    return (delta <= rhs - lhs);
  }
  Formula VisitConjunction(const Formula& f, const double delta) const {
    return make_conjunction(
        map(get_operands(f), [this, delta](const Formula& formula) {
          return this->Visit(formula, delta);
        }));
  }
  Formula VisitDisjunction(const Formula& f, const double delta) const {
    return make_disjunction(
        map(get_operands(f), [this, delta](const Formula& formula) {
          return this->Visit(formula, delta);
        }));
  }
  Formula VisitNegation(const Formula& f, const double delta) const {
    return !Visit(get_operand(f), -delta);
  }
  Formula VisitForall(const Formula&, const double) const {
    throw runtime_error{
        "DeltaStrengthenVisitor: forall formula is not supported."};
  }

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula>(
      const DeltaStrengthenVisitor*, const Formula&, const double&);
};
}  // namespace

/// Strengthen the input formula $p f by @p delta.
Formula DeltaStrengthen(const Formula& f, const double delta) {
  assert(delta > 0);
  return DeltaStrengthenVisitor{}.Strengthen(f, delta);
}

/// Weaken the input formula $p f by @p delta.
Formula DeltaWeaken(const Formula& f, const double delta) {
  assert(delta > 0);
  return DeltaStrengthenVisitor{}.Strengthen(f, -delta);
}

}  // namespace dreal
