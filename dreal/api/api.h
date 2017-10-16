#pragma once

#include <experimental/optional>

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

/// Checks the satisfiability of a given formula @p f with a given precision
/// @p delta.
///
/// @returns a model, a mapping from a variable to an interval, if @p f is
/// δ-satisfiable.
/// @returns a nullopt, if @p is unsatisfiable.
std::experimental::optional<Box> CheckSatisfiability(const Formula& f,
                                                     double delta);

/// Checks the satisfiability of a given formula @p f with a given precision
/// @p delta.
///
/// @returns true if it finds a model which will be saved in @p box.
/// @returns false if it concludes unsat.
///
/// @note We provide this version of API to avoid the use of
/// std::experimental::optional.
bool CheckSatisfiability(const Formula& f, double delta, Box* box);

/// Finds a solution to minimize @p objective function while satisfying a
/// given @p constraint using @p delta.
///
/// @returns a model, a mapping from a variable to an interval, if a solution
/// exists.
/// @returns nullopt, if there is no solution.
std::experimental::optional<Box> Minimize(const Expression& objective,
                                          const Formula& constraint,
                                          double delta);

/// Finds a solution to minimize @p objective function while satisfying a
/// given @p constraint using @p delta.
///
/// @returns true if it finds a model which will be saved in @p box.
/// @returns false if it concludes unsat.
///
/// @note We provide this version of API to avoid the use of
/// std::experimental::optional.
bool Minimize(const Expression& objective, const Formula& constraint,
              double delta, Box* box);

}  // namespace dreal
