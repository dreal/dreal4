#pragma once

#include <set>
#include <unordered_map>
#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/solver/config.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/solver/icp.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/optional.h"

namespace dreal {

/// Theory solver for nonlinear theory over the Reals.
class TheorySolver {
 public:
  TheorySolver() = delete;
  explicit TheorySolver(const Config& config);

  /// Checks consistency. Returns true if there is a satisfying
  /// assignment. Otherwise, return false.
  bool CheckSat(const Box& box, const std::vector<Formula>& assertions);

  /// Gets a satisfying Model.
  const Box& GetModel() const;

  /// Gets a list of used constraints.
  const std::set<Formula>& GetExplanation() const;

 private:
  // Builds a contractor using @p box and @p assertions. It returns
  // nullopt if it detects an empty box while building a contractor.
  //
  // @note This method updates @p box as it calls FilterAssertion
  // function.
  optional<Contractor> BuildContractor(const std::vector<Formula>& assertions,
                                       ContractorStatus* contractor_status);
  std::vector<FormulaEvaluator> BuildFormulaEvaluator(
      const std::vector<Formula>& assertions);

  const Config& config_;
  Icp icp_;
  Box model_;
  std::set<Formula> explanation_;
  std::unordered_map<Formula, Contractor> contractor_cache_;
  std::unordered_map<Formula, FormulaEvaluator> formula_evaluator_cache_;
};

}  // namespace dreal
