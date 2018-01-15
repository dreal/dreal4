#pragma once

#include <map>
#include <unordered_map>
#include <vector>

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/naive_cnfizer.h"

namespace dreal {
/// Transforms a symbolic formula @p f into an equi-satisfiable CNF
/// formula by introducing extra Boolean variables (Tseitin transformation).
class TseitinCnfizer {
 public:
  /// Convert @p f into an equi-satisfiable formula @c f' in CNF.
  std::vector<Formula> Convert(const Formula& f);

  /// Returns a const reference of `map_` member.
  ///
  /// @note that this member `map_` is cleared at the beginning of `Convert`
  /// method.
  const std::map<Variable, Formula>& map() const { return map_; }

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

  // Maps a temporary variable, which is introduced by a Tseitin
  // transformation, to a corresponding Formula.
  //
  // @note that this map_ is cleared at the beginning of `Convert`
  // call.
  std::map<Variable, Formula> map_;

  // To transform nested formulas inside of universal quantifications.
  const NaiveCnfizer naive_cnfizer_{};

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend Formula drake::symbolic::VisitFormula<Formula, TseitinCnfizer>(
      TseitinCnfizer*, const Formula&);
};
}  // namespace dreal
