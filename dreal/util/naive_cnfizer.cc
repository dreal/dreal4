#include "dreal/util/naive_cnfizer.h"

#include <numeric>
#include <set>

#include "dreal/util/assert.h"
#include "dreal/util/exception.h"

namespace dreal {

using std::accumulate;
using std::set;

// The main function of the NaiveCnfizer:
//  - It visits each node and introduce a Boolean variable `b` for
//    each subterm `f`, and keep the relation `b ⇔ f`.
//  - Then it cnfizes each `b ⇔ f` and make a conjunction of them.
Formula NaiveCnfizer::Convert(const Formula& f) const {
  // TODO(soonho): Using cache if needed.
  return Visit(nnfizer_.Convert(f, true /* push_negation_into_relationals */));
}

Formula NaiveCnfizer::Visit(const Formula& f) const {
  return VisitFormula<Formula>(this, f);
}
Formula NaiveCnfizer::VisitFalse(const Formula& f) const { return f; }
Formula NaiveCnfizer::VisitTrue(const Formula& f) const { return f; }
Formula NaiveCnfizer::VisitVariable(const Formula& f) const { return f; }
Formula NaiveCnfizer::VisitEqualTo(const Formula& f) const {
  const Expression& lhs{get_lhs_expression(f)};
  const Expression& rhs{get_rhs_expression(f)};
  return (lhs >= rhs) && (lhs <= rhs);
}
Formula NaiveCnfizer::VisitNotEqualTo(const Formula& f) const {
  const Expression& lhs{get_lhs_expression(f)};
  const Expression& rhs{get_rhs_expression(f)};
  return (lhs > rhs) || (lhs < rhs);
}
Formula NaiveCnfizer::VisitGreaterThan(const Formula& f) const { return f; }
Formula NaiveCnfizer::VisitGreaterThanOrEqualTo(const Formula& f) const {
  return f;
}
Formula NaiveCnfizer::VisitLessThan(const Formula& f) const { return f; }
Formula NaiveCnfizer::VisitLessThanOrEqualTo(const Formula& f) const {
  return f;
}
Formula NaiveCnfizer::VisitForall(const Formula& f) const {
  // f = ∀y. φ(x, y).
  const Variables& quantified_variables{get_quantified_variables(f)};  // y
  const Formula& quantified_formula{get_quantified_formula(f)};  // φ(x, y)
  return forall(quantified_variables, Convert(quantified_formula));
}

Formula NaiveCnfizer::VisitConjunction(const Formula& f) const {
  const set<Formula> transformed_operands{
      map(get_operands(f),
          [this](const Formula& formula) { return this->Visit(formula); })};
  return make_conjunction(transformed_operands);
}

Formula NaiveCnfizer::VisitDisjunction(const Formula& f) const {
  const set<Formula>& transformed_operands{
      map(get_operands(f),
          [this](const Formula& formula) { return this->Visit(formula); })};
  return accumulate(transformed_operands.begin(), transformed_operands.end(),
                    Formula::False(),
                    [](const Formula& cnf1, const Formula& cnf2) {
                      set<Formula> clauses;
                      if (is_conjunction(cnf1)) {
                        if (is_conjunction(cnf2)) {
                          // Both of cnf1 and cnf2 are conjunctions.
                          for (const Formula& c1 : get_operands(cnf1)) {
                            for (const Formula& c2 : get_operands(cnf2)) {
                              clauses.insert(c1 || c2);
                            }
                          }
                        } else {
                          // Only cnf1 is a conjunction.
                          for (const Formula& c1 : get_operands(cnf1)) {
                            clauses.insert(c1 || cnf2);
                          }
                        }
                      } else {
                        if (is_conjunction(cnf2)) {
                          // Only cnf2 is a conjunction.
                          for (const Formula& c2 : get_operands(cnf2)) {
                            clauses.insert(cnf1 || c2);
                          }
                        } else {
                          // None of them is a conjunction.
                          clauses.insert(cnf1 || cnf2);
                        }
                      }
                      return make_conjunction(clauses);
                    });
}

Formula NaiveCnfizer::VisitNegation(const Formula& f) const {
  DREAL_ASSERT(is_atomic(get_operand(f)));
  return f;
}
}  // namespace dreal
