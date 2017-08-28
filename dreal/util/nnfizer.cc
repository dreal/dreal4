#include "dreal/util/nnfizer.h"

#include <set>

namespace dreal {

using std::set;

Formula Nnfizer::Convert(const Formula& f,
                         const bool push_negation_into_relationals) const {
  return Visit(f, true, push_negation_into_relationals);
}

Formula Nnfizer::Visit(const Formula& f, const bool polarity,
                       const bool push_negation_into_relationals) const {
  return VisitFormula<Formula>(this, f, polarity,
                               push_negation_into_relationals);
}

Formula Nnfizer::VisitFalse(const Formula&, const bool polarity,
                            const bool) const {
  // NNF(False)  = False
  // NNF(¬False) = True
  return polarity ? Formula::False() : Formula::True();
}
Formula Nnfizer::VisitTrue(const Formula&, const bool polarity,
                           const bool) const {
  // NNF(True)  = True
  // NNF(¬True) = False
  return polarity ? Formula::True() : Formula::False();
}
Formula Nnfizer::VisitVariable(const Formula& f, const bool polarity,
                               const bool) const {
  // NNF(b)  = b
  // NNF(¬b) = ¬b
  return polarity ? f : !f;
}
Formula Nnfizer::VisitEqualTo(const Formula& f, const bool polarity,
                              const bool push_negation_into_relationals) const {
  if (polarity) {
    return f;
  } else {
    if (push_negation_into_relationals) {
      // ¬(e₁ = e₂) ↦ (e₁ ≠ e₂)
      return get_lhs_expression(f) != get_rhs_expression(f);
    } else {
      return !f;
    }
  }
}

Formula Nnfizer::VisitNotEqualTo(
    const Formula& f, const bool polarity,
    const bool push_negation_into_relationals) const {
  if (polarity) {
    return f;
  } else {
    if (push_negation_into_relationals) {
      // ¬(e₁ ≠ e₂) ↦ (e₁ = e₂)
      return get_lhs_expression(f) == get_rhs_expression(f);
    } else {
      return !f;
    }
  }
}
Formula Nnfizer::VisitGreaterThan(
    const Formula& f, const bool polarity,
    const bool push_negation_into_relationals) const {
  if (polarity) {
    return f;
  } else {
    if (push_negation_into_relationals) {
      // ¬(e₁ > e₂) ↦ (e₁ <= e₂)
      return get_lhs_expression(f) <= get_rhs_expression(f);
    } else {
      return !f;
    }
  }
}
Formula Nnfizer::VisitGreaterThanOrEqualTo(
    const Formula& f, const bool polarity,
    const bool push_negation_into_relationals) const {
  if (polarity) {
    return f;
  } else {
    if (push_negation_into_relationals) {
      // ¬(e₁ >= e₂) ↦ (e₁ < e₂)
      return get_lhs_expression(f) < get_rhs_expression(f);
    } else {
      return !f;
    }
  }
}
Formula Nnfizer::VisitLessThan(
    const Formula& f, const bool polarity,
    const bool push_negation_into_relationals) const {
  if (polarity) {
    return f;
  } else {
    if (push_negation_into_relationals) {
      // ¬(e₁ < e₂) ↦ (e₁ >= e₂)
      return get_lhs_expression(f) >= get_rhs_expression(f);
    } else {
      return !f;
    }
  }
}
Formula Nnfizer::VisitLessThanOrEqualTo(
    const Formula& f, const bool polarity,
    const bool push_negation_into_relationals) const {
  if (polarity) {
    return f;
  } else {
    if (push_negation_into_relationals) {
      // ¬(e₁ <= e₂) ↦ (e₁ > e₂)
      return get_lhs_expression(f) > get_rhs_expression(f);
    } else {
      return !f;
    }
  }
}
Formula Nnfizer::VisitConjunction(
    const Formula& f, const bool polarity,
    const bool push_negation_into_relationals) const {
  // NNF(f₁ ∧ ... ∨ fₙ)    = NNF(f₁) ∧ ... ∧ NNF(fₙ)
  // NNF(¬(f₁ ∧ ... ∨ fₙ)) = NNF(¬f₁) ∨ ... ∨ NNF(¬fₙ)
  const set<Formula> new_operands{map(
      get_operands(f),
      [this, polarity, push_negation_into_relationals](const Formula& formula) {
        return this->Visit(formula, polarity, push_negation_into_relationals);
      })};
  return polarity ? make_conjunction(new_operands)
                  : make_disjunction(new_operands);
}
Formula Nnfizer::VisitDisjunction(
    const Formula& f, const bool polarity,
    const bool push_negation_into_relationals) const {
  // NNF(f₁ ∨ ... ∨ fₙ)    = NNF(f₁) ∨ ... ∨ NNF(fₙ)
  // NNF(¬(f₁ ∨ ... ∨ fₙ)) = NNF(¬f₁) ∧ ... ∧ NNF(¬fₙ)
  const set<Formula> new_operands{map(
      get_operands(f),
      [this, polarity, push_negation_into_relationals](const Formula& formula) {
        return this->Visit(formula, polarity, push_negation_into_relationals);
      })};
  return polarity ? make_disjunction(new_operands)
                  : make_conjunction(new_operands);
}
Formula Nnfizer::VisitNegation(
    const Formula& f, const bool polarity,
    const bool push_negation_into_relationals) const {
  // NNF(¬f, ⊤) = NNF(f, ⊥)
  // NNF(¬f, ⊥) = NNF(f, ⊤)
  return Visit(get_operand(f), !polarity, push_negation_into_relationals);
}
Formula Nnfizer::VisitForall(const Formula& f, const bool polarity,
                             const bool) const {
  // NNF(∀v₁...vₙ. f)    =  ∀v₁...vₙ. f
  // NNF(¬(∀v₁...vₙ. f)) = ¬∀v₁...vₙ. f
  //
  // TODO(soonho-tri): The second case can be further reduced into
  // ∃v₁...vₙ. NNF(¬f). However, we do not have a representation
  // FormulaExists(∃) yet. Revisit this when we add FormulaExists.
  return polarity ? f : !f;
}
}  // namespace dreal
