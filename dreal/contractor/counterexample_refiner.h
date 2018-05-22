#pragma once

#include <memory>
#include <vector>

#include "dreal/optimization/nlopt_optimizer.h"
#include "dreal/solver/config.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

/// Refines a counterexample using local optimizations.  This is used
/// to refine counterexamples found by the forall contractor (in
/// contractor_forall.h).
class CounterexampleRefiner {
 public:
  /// Constructs CounterexampleRefiner.
  /// @param query Counterexample query. It should be either a relational
  ///              formula or a conjunction of relational formulas.
  /// @param forall_variables universally quantified variables. They are
  ///                         decision variables that we consider in the
  ///                         local optimization.
  /// @param config Configuration to use for finding counterexamples.
  ///
  /// @pre @p query is a conjunction.
  CounterexampleRefiner(const Formula& query, Variables forall_variables,
                        const Config& config);

  /// Refines an initial solution and returns an improved one if possible.
  Box Refine(Box box);

 private:
  std::unique_ptr<NloptOptimizer> opt_;

  // Initial vector which will be fed to Nlopt. Note that the Nlopt
  // will update this variable with a found solution.
  std::vector<double> init_;

  std::vector<Variable> forall_vec_;

  const Variables forall_variables_;
};
}  // namespace dreal
