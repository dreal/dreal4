#pragma once
#include "dreal/symbolic/symbolic.h"

namespace dreal {

/// A class implementing NNF (Negation Normal Form) conversion. See
/// https://en.wikipedia.org/wiki/Negation_normal_form for more
/// information on NNF. When `push_negation_into_relationals` is true, it pushed
/// negations into relational formulas by flipping relational
/// operators. For example, `¬(x >= 10)` is transformed into `(x <
/// 10)`.
class Nnfizer {
 public:
  /// Converts @p f into an equivalent formula @c f' in NNF.
  Formula Convert(const Formula& f,
                  bool push_negation_into_relationals = false) const;

 private:
  // Converts @p f into an equivalent formula @c f' in NNF. The parameter @p
  // polarity is to indicate whether it processes @c f (if @p polarity is
  // true) or @c ¬f (if @p polarity is false).
  Formula Visit(const Formula& f, bool polarity,
                bool push_negation_into_relationals) const;

  Formula VisitFalse(const Formula& f, bool polarity,
                     bool push_negation_into_relationals) const;
  Formula VisitTrue(const Formula& f, bool polarity,
                    bool push_negation_into_relationals) const;
  Formula VisitVariable(const Formula& f, bool polarity,
                        bool push_negation_into_relationals) const;
  Formula VisitEqualTo(const Formula& f, bool polarity,
                       bool push_negation_into_relationals) const;
  Formula VisitNotEqualTo(const Formula& f, bool polarity,
                          bool push_negation_into_relationals) const;
  Formula VisitGreaterThan(const Formula& f, bool polarity,
                           bool push_negation_into_relationals) const;
  Formula VisitGreaterThanOrEqualTo(const Formula& f, bool polarity,
                                    bool push_negation_into_relationals) const;
  Formula VisitLessThan(const Formula& f, bool polarity,
                        bool push_negation_into_relationals) const;
  Formula VisitLessThanOrEqualTo(const Formula& f, bool polarity,
                                 bool push_negation_into_relationals) const;
  Formula VisitConjunction(const Formula& f, bool polarity,
                           bool push_negation_into_relationals) const;
  Formula VisitDisjunction(const Formula& f, bool polarity,
                           bool push_negation_into_relationals) const;
  Formula VisitNegation(const Formula& f, bool polarity,
                        bool push_negation_into_relationals) const;
  Formula VisitForall(const Formula& f, bool polarity,
                      bool push_negation_into_relationals) const;

  // Makes VisitFormula a friend of this class so that it can use private
  // methods.
  friend Formula drake::symbolic::VisitFormula<Formula>(const Nnfizer*,
                                                        const Formula&,
                                                        const bool&,
                                                        const bool&);
};
}  // namespace dreal
