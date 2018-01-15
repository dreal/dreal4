#pragma once

#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <experimental/optional>

#include "dreal/contractor/contractor.h"
#include "dreal/solver/config.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

class TheorySolver {
 public:
  TheorySolver() = delete;
  TheorySolver(const Config& config, const Box& box);

  /// Checks consistency. Returns true if there is a satisfying
  /// assignment. Otherwise, return false.
  bool CheckSat(const Box& box, const std::vector<Formula>& assertions);

  /// Gets a satisfying Model.
  Box GetModel() const;

  /// Gets a list of used constraints.
  const std::unordered_set<Formula, hash_value<Formula>> GetExplanation() const;

 private:
  // Builds a contractor using @p box and @p assertions. It returns
  // nullopt if it detects an empty box while building a contractor.
  //
  // @note This method updates @p box as it calls FilterAssertion
  // function.
  std::experimental::optional<Contractor> BuildContractor(
      const std::vector<Formula>& assertions);
  std::vector<FormulaEvaluator> BuildFormulaEvaluator(
      const std::vector<Formula>& assertions);

  const Config& config_;
  ContractorStatus contractor_status_;

  std::unordered_map<Formula, Contractor, hash_value<Formula>>
      contractor_cache_;
  std::unordered_map<Formula, FormulaEvaluator, hash_value<Formula>>
      formula_evaluator_cache_;
};

}  // namespace dreal
