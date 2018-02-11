#pragma once

#include "dreal/contractor/contractor.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

/// Converts an arbitrary formula into a contractor. This is used in
/// the forall contractor.
class GenericContractorGenerator {
 public:
  /// Generates @p f into a contractor using @p box. It converts a
  /// conjunction `f₁ ∧ ... ∧ fₙ` into a sequential contractor
  /// `ContractorSeq(c(f₁), ..., c(fₙ))`. For a disjunction `f₁ ∨
  /// ... ∨ fₙ`, this method transforms it into a join contractor
  /// `ContractorJoin(c(f₁), ..., c(fₙ))`.
  ///
  /// When @p use_polytope is true, it adds IbexPolytope contractor
  /// when it processes conjunctions. Otherwise, it uses
  /// `ContractorIbexFwdbwd`.
  Contractor Generate(const Formula& f, const Box& box,
                      const Config& config) const;

 private:
  Contractor Visit(const Formula& f, const Box& box,
                   const Config& config) const;
  Contractor VisitFalse(const Formula&, const Box&, const Config& config) const;
  Contractor VisitTrue(const Formula&, const Box&, const Config& config) const;
  Contractor VisitVariable(const Formula&, const Box&,
                           const Config& config) const;
  Contractor VisitEqualTo(const Formula& f, const Box& box,
                          const Config& config) const;
  Contractor VisitNotEqualTo(const Formula& f, const Box& box,
                             const Config& config) const;
  Contractor VisitGreaterThan(const Formula& f, const Box& box,
                              const Config& config) const;
  Contractor VisitGreaterThanOrEqualTo(const Formula& f, const Box& box,
                                       const Config& config) const;
  Contractor VisitLessThan(const Formula& f, const Box& box,
                           const Config& config) const;
  Contractor VisitLessThanOrEqualTo(const Formula& f, const Box& box,
                                    const Config& config) const;
  Contractor VisitConjunction(const Formula& f, const Box& box,
                              const Config& config) const;
  Contractor VisitDisjunction(const Formula& f, const Box& box,
                              const Config& config) const;
  Contractor VisitNegation(const Formula& f, const Box&,
                           const Config& config) const;
  Contractor VisitForall(const Formula&, const Box&,
                         const Config& config) const;

  // Makes VisitFormula a friend of this class so that it can use private
  // methods.
  friend Contractor drake::symbolic::VisitFormula<Contractor>(
      const GenericContractorGenerator*, const Formula&, const dreal::Box&,
      const Config&);
};
}  // namespace dreal
