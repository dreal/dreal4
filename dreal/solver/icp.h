#pragma once

#include <vector>
#include <experimental/optional>

#include "dreal/contractor/contractor.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

/// Class for ICP (Interval Constraint Propagation) algorithm.
class Icp {
 public:
  Icp(Contractor contractor, std::vector<FormulaEvaluator> formula_evaluators,
      double precision);

  /// Checks the delta-satisfiability of the current assertions.
  /// Returns true  if it's delta-SAT.
  /// Returns false if it's UNSAT.
  bool CheckSat(ContractorStatus* cs);

 private:
  // Evaluates each assertion fᵢ with @p box.
  //
  // Returns None                if there is fᵢ such that fᵢ(box) is empty.
  //                             (This indicates the problem is UNSAT)
  //
  // Returns Some(∅)            if for all fᵢ, we have |fᵢ(B)| ≤ δ.
  //                             (This indicates the problem is delta-SAT)
  //
  // Returns Some(Vars)          if there is fᵢ such that |fᵢ(B)| > δ.
  //                             Vars = {v | v ∈ fᵢ ∧ |fᵢ(B)| > δ for all fᵢs}.
  //                             (This indicates the problem is delta-SAT)
  std::experimental::optional<ibex::BitSet> EvaluateBox(const Box& box);

  const Contractor contractor_;
  std::vector<FormulaEvaluator> formula_evaluators_;
  const double precision_{};
};

}  // namespace dreal
