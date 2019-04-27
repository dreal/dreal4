#pragma once

#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_status.h"
#include "dreal/solver/config.h"
#include "dreal/solver/formula_evaluator.h"

namespace dreal {

/// Abstract Class for ICP (Interval Constraint Propagation) algorithm.
class Icp {
 public:
  /// Constructs an Icp based on @p config.
  explicit Icp(const Config& config) : config_{config} {}
  virtual ~Icp() = default;

  /// Checks the delta-satisfiability of the current assertions.
  /// @param[in] contractor Contractor to use in pruning phase
  /// @param[in] formula_evaluators A vector of FormulaEvaluator which
  ///                               determines when to stop and which
  ///                               dimension to branch.
  /// @param[in,out] cs A contractor to be updated.
  /// Returns true  if it's delta-SAT.
  /// Returns false if it's UNSAT.
  virtual bool CheckSat(const Contractor& contractor,
                        const std::vector<FormulaEvaluator>& formula_evaluators,
                        ContractorStatus* cs) = 0;

 protected:
  const Config& config_;
};

}  // namespace dreal
