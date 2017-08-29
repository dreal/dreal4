#pragma once

#include <memory>
#include <unordered_map>
#include <vector>

#include "dreal/symbolic/symbolic.h"

namespace dreal {
class PredicateAbstractor {
 public:
  Formula Convert(const Formula& f);
  Formula Convert(const std::vector<Formula>& formulas);

  std::unordered_map<Variable, Formula, hash_value<Variable>>
  var_to_formula_map() const {
    return var_to_formula_map_;
  }
  std::unordered_map<Formula, Variable, hash_value<Formula>>
  formula_to_var_map() const {
    return formula_to_var_map_;
  }

 private:
  Formula Visit(const Formula& f);
  Formula VisitFalse(const Formula& f);
  Formula VisitTrue(const Formula& f);
  Formula VisitVariable(const Formula& f);
  Formula VisitAtomic(const Formula& f);
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

  void Add(const Variable& var, const Formula& f);

  std::unordered_map<Variable, Formula, hash_value<Variable>>
      var_to_formula_map_;
  std::unordered_map<Formula, Variable, hash_value<Formula>>
      formula_to_var_map_;

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula, PredicateAbstractor>(
      PredicateAbstractor*, const Formula&);
};
}  // namespace dreal
