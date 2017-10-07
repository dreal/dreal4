#pragma once

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/nnfizer.h"

namespace dreal {
/// Transforms a symbolic formula @p f into a CNF formula by
/// preserving its semantics.
///
/// @note This transform can increase the size exponentially. We are
/// using this transformation in TseitinCnfizer when we process the
/// nested formula in a universally quantified formula.
class NaiveCnfizer {
 public:
  /// Convert @p f into its CNF form.
  Formula Convert(const Formula& f) const;

 private:
  Formula Visit(const Formula& f) const;
  Formula VisitFalse(const Formula& f) const;
  Formula VisitTrue(const Formula& f) const;
  Formula VisitVariable(const Formula& f) const;
  Formula VisitEqualTo(const Formula& f) const;
  Formula VisitNotEqualTo(const Formula& f) const;
  Formula VisitGreaterThan(const Formula& f) const;
  Formula VisitGreaterThanOrEqualTo(const Formula& f) const;
  Formula VisitLessThan(const Formula& f) const;
  Formula VisitLessThanOrEqualTo(const Formula& f) const;
  Formula VisitConjunction(const Formula& f) const;
  Formula VisitDisjunction(const Formula& f) const;
  Formula VisitNegation(const Formula& f) const;
  Formula VisitForall(const Formula& f) const;

  const Nnfizer nnfizer_{};

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula>(const NaiveCnfizer*,
                                                        const Formula&);
};
}  // namespace dreal
