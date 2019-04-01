#pragma once

#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/optional.h"

namespace dreal {

/// Class for ICP (Interval Constraint Propagation) algorithm.
class Icp {
 public:
  /// Constructs an Icp based on @p config.
  explicit Icp(const Config& config);

  /// Checks the delta-satisfiability of the current assertions.
  /// @param[in] contractor Contractor to use in pruning phase
  /// @param[in] formula_evaluators A vector of FormulaEvaluator which
  ///                           determines when to stop and which
  ///                           dimension to branch.
  /// @param[in,out] cs A contractor to be updated.
  /// Returns true  if it's delta-SAT.
  /// Returns false if it's UNSAT.
  bool CheckSat(const Contractor& contractor,
                const std::vector<FormulaEvaluator>& formula_evaluators,
                ContractorStatus* cs);

 private:
  // Evaluates each assertion fᵢ with @p box.
  //
  // Returns None                if there is fᵢ such that fᵢ(box) is empty.
  //                             (This indicates the problem is UNSAT)
  //
  // Returns Some(∅)             if for all fᵢ, we have either
  //                             1) fᵢ(x) is valid for all x ∈ B *or*
  //                             2) |fᵢ(B)| ≤ δ.
  //                             (This indicates the problem is delta-SAT)
  //
  // Returns Some(Vars)          if there is fᵢ such that
  //                             1) Interval arithmetic can't validate that
  //                                fᵢ(x) is valid for all x ∈ B *and*
  //                             2) |fᵢ(B)| > δ.
  //                             Vars = {v | v ∈ fᵢ ∧ |fᵢ(B)| > δ for all fᵢs}.
  //                             (This indicates the problem is delta-SAT)
  //
  // It sets @p cs's box empty if it detects UNSAT. It also calls
  // cs->AddUsedConstraint to store the constraint that is responsible
  // for the UNSAT.
  optional<ibex::BitSet> EvaluateBox(
      const std::vector<FormulaEvaluator>& formula_evaluators, const Box& box,
      ContractorStatus* cs);

  const Config& config_;

  // If `stack_left_box_first_` is true, we add the left box from the
  // branching operation to the `stack`. Otherwise, we add the right
  // box first.
  bool stack_left_box_first_{false};
};

}  // namespace dreal
