#include "dreal/symbolic/symbolic.h"

#include <algorithm>
#include <iterator>

#include "dreal/util/assert.h"
#include "dreal/util/exception.h"

namespace dreal {

using std::function;
using std::inserter;
using std::ostream;
using std::set;
using std::string;
using std::to_string;
using std::transform;
using std::vector;

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
    case FormulaKind::Not: {
      const Formula& negated_formula{get_operand(f)};
      return is_variable(negated_formula) || is_relational(negated_formula);
    }
  }
  DREAL_UNREACHABLE();
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
  DREAL_UNREACHABLE();
}

set<Formula> get_clauses(const Formula& f) {
  if (is_conjunction(f)) {
#ifndef NDEBUG
    for (const Formula& clause : get_operands(f)) {
      DREAL_ASSERT(is_clause(clause));
    }
#endif
    return get_operands(f);
  } else {
    DREAL_ASSERT(is_clause(f));
    return {f};
  }
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
  DREAL_UNREACHABLE();
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
    throw DREAL_RUNTIME_ERROR(
        "DeltaStrengthenVisitor: forall formula is not supported.");
  }

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula>(
      const DeltaStrengthenVisitor*, const Formula&, const double&);
};
}  // namespace

/// Strengthen the input formula $p f by @p delta.
Formula DeltaStrengthen(const Formula& f, const double delta) {
  DREAL_ASSERT(delta > 0);
  return DeltaStrengthenVisitor{}.Strengthen(f, delta);
}

/// Weaken the input formula $p f by @p delta.
Formula DeltaWeaken(const Formula& f, const double delta) {
  DREAL_ASSERT(delta > 0);
  return DeltaStrengthenVisitor{}.Strengthen(f, -delta);
}

Formula make_conjunction(const vector<Formula>& formulas) {
  return make_conjunction(set<Formula>(formulas.begin(), formulas.end()));
}

Formula make_disjunction(const vector<Formula>& formulas) {
  return make_disjunction(set<Formula>(formulas.begin(), formulas.end()));
}

vector<Variable> CreateVector(const string& prefix, const int size,
                              const Variable::Type type) {
  DREAL_ASSERT(prefix.length() > 0);
  DREAL_ASSERT(size >= 1);
  vector<Variable> v;
  for (int i = 0; i < size; ++i) {
    v.emplace_back(prefix + to_string(i), type);
  }
  return v;
}

RelationalOperator operator!(const RelationalOperator op) {
  switch (op) {
    case RelationalOperator::EQ:
      return RelationalOperator::NEQ;

    case RelationalOperator::NEQ:
      return RelationalOperator::EQ;

    case RelationalOperator::GT:
      return RelationalOperator::LEQ;

    case RelationalOperator::GEQ:
      return RelationalOperator::LT;

    case RelationalOperator::LT:
      return RelationalOperator::GEQ;

    case RelationalOperator::LEQ:
      return RelationalOperator::GT;
  }
  DREAL_UNREACHABLE();
}

ostream& operator<<(ostream& os, const RelationalOperator op) {
  switch (op) {
    case RelationalOperator::EQ:
      return os << "=";

    case RelationalOperator::NEQ:
      return os << "≠";

    case RelationalOperator::GT:
      return os << ">";

    case RelationalOperator::GEQ:
      return os << "≥";

    case RelationalOperator::LT:
      return os << "<";

    case RelationalOperator::LEQ:
      return os << "≤";
  }
  DREAL_UNREACHABLE();
}

}  // namespace dreal
