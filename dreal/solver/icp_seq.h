#pragma once

#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_status.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/solver/icp.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/optional.h"

namespace dreal {

/// Class for ICP (Interval Constraint Propagation) algorithm.
class IcpSeq : public Icp {
 public:
  /// Constructs an IcpSeq based on @p config.
  explicit IcpSeq(const Config& config);

  bool CheckSat(const Contractor& contractor,
                const std::vector<FormulaEvaluator>& formula_evaluators,
                ContractorStatus* cs) override;

 private:
  // Evaluates each formula with @p box using interval
  // arithmetic. There are three possible outcomes:
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
  //                             Vars = {v | v ∈ fᵢ ∧ |fᵢ(B)| > δ for all
  //                             fᵢs}.
  //
  //                             It cannot conclude if the constraint
  //                             is satisfied or not completely. It
  //                             checks the width/diameter of the
  //                             interval evaluation and adds the free
  //                             variables in the constraint into the
  //                             set that it will return.
  //
  // If it returns an ibex::BitSet, it represents the dimensions on
  // which the ICP algorithm needs to consider branching.
  //
  // It sets @p cs's box empty if it detects UNSAT. It also calls
  // cs->AddUsedConstraint to store the constraint that is responsible
  // for the UNSAT.
  optional<ibex::BitSet> EvaluateBox(
      const std::vector<FormulaEvaluator>& formula_evaluators, const Box& box,
      ContractorStatus* cs);

  // If `stack_left_box_first_` is true, we add the left box from the
  // branching operation to the `stack`. Otherwise, we add the right
  // box first.
  bool stack_left_box_first_{false};
};

}  // namespace dreal
