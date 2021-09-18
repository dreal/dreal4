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

#include "dreal/solver/config.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/optional.h"

namespace dreal {

/// Checks the satisfiability of a given formula @p f with a given precision
/// @p delta.
///
/// @returns a model, a mapping from a variable to an interval, if @p f is
/// δ-satisfiable.
/// @returns a nullopt, if @p is unsatisfiable.
optional<Box> CheckSatisfiability(const Formula& f, double delta);

/// Checks the satisfiability of a given formula @p f with a given configuration
/// @p config.
optional<Box> CheckSatisfiability(const Formula& f, Config config);

/// Checks the satisfiability of a given formula @p f with a given precision
/// @p delta.
///
/// @returns true if it finds a model which will be saved in @p box.
/// @returns false if it concludes unsat.
///
/// @note We provide this version of API to avoid the use of optional.
bool CheckSatisfiability(const Formula& f, double delta, Box* box);

/// Checks the satisfiability of a given formula @p f with a given configuration
/// @p config.
bool CheckSatisfiability(const Formula& f, Config config, Box* box);

/// Finds a solution to minimize @p objective function while satisfying a
/// given @p constraint using @p delta.
///
/// @returns a model, a mapping from a variable to an interval, if a solution
/// exists.
/// @returns nullopt, if there is no solution.
optional<Box> Minimize(const Expression& objective, const Formula& constraint,
                       double delta);

/// Finds a solution to minimize @p objective function while satisfying a
/// given @p constraint using @p delta.
optional<Box> Minimize(const Expression& objective, const Formula& constraint,
                       Config config);

/// Finds a solution to minimize @p objective function while satisfying a
/// given @p constraint using @p delta.
///
/// @returns true if it finds a model which will be saved in @p box.
/// @returns false if it concludes unsat.
///
/// @note We provide this version of API to avoid the use of optional.
bool Minimize(const Expression& objective, const Formula& constraint,
              double delta, Box* box);

/// Finds a solution to minimize @p objective function while satisfying a
/// given @p constraint using @p delta.
bool Minimize(const Expression& objective, const Formula& constraint,
              Config config, Box* box);

}  // namespace dreal
