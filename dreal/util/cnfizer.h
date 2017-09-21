#pragma once

#include <unordered_map>
#include <vector>

#include "dreal/symbolic/symbolic.h"

namespace dreal {

/// Transforms a symbolic formula @p f into an equi-satisfiable CNF
/// formula by introducing extra Boolean variables.
class Cnfizer {
 public:
  /// Convert @p f into an equi-satisfiable formula @c f' in CNF.
  std::vector<Formula> Convert(const Formula& f);

 private:
  Formula Visit(const Formula& f);
  Formula VisitFalse(const Formula& f);
  Formula VisitTrue(const Formula& f);
  Formula VisitVariable(const Formula& f);
  Formula VisitEqualTo(const Formula& f);
  Formula VisitNotEqualTo(const Formula& f);
  Formula VisitGreaterThan(const Formula& f);
  Formula VisitGreaterThanOrEqualTo(const Formula& f);
  Formula VisitLessThan(const Formula& f);
  Formula VisitLessThanOrEqualTo(const Formula& f);
  Formula VisitConjunction(const Formula& f);
  Formula VisitDisjunction(const Formula& f);
  Formula VisitNegation(const Formula& f);
  Formula VisitForall(const Formula& f);

  std::unordered_map<Variable, Formula, hash_value<Variable>> map_;

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula, Cnfizer>(
      Cnfizer*, const Formula&);
};
}  // namespace dreal
