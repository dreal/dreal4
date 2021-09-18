/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
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
