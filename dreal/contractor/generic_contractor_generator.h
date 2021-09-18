/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
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
  static Contractor VisitFalse(const Formula&, const Box&,
                               const Config& config);
  static Contractor VisitTrue(const Formula&, const Box&, const Config& config);
  static Contractor VisitVariable(const Formula&, const Box&,
                                  const Config& config);
  static Contractor VisitEqualTo(const Formula& f, const Box& box,
                                 const Config& config);
  static Contractor VisitNotEqualTo(const Formula& f, const Box& box,
                                    const Config& config);
  static Contractor VisitGreaterThan(const Formula& f, const Box& box,
                                     const Config& config);
  static Contractor VisitGreaterThanOrEqualTo(const Formula& f, const Box& box,
                                              const Config& config);
  static Contractor VisitLessThan(const Formula& f, const Box& box,
                                  const Config& config);
  static Contractor VisitLessThanOrEqualTo(const Formula& f, const Box& box,
                                           const Config& config);
  Contractor VisitConjunction(const Formula& f, const Box& box,
                              const Config& config) const;
  Contractor VisitDisjunction(const Formula& f, const Box& box,
                              const Config& config) const;
  static Contractor VisitNegation(const Formula& f, const Box&,
                                  const Config& config);
  static Contractor VisitForall(const Formula&, const Box&,
                                const Config& config);

  // Makes VisitFormula a friend of this class so that it can use private
  // methods.
  friend Contractor drake::symbolic::VisitFormula<Contractor>(
      const GenericContractorGenerator*, const Formula&, const dreal::Box&,
      const Config&);
};
}  // namespace dreal
