#pragma once

#include <cmath>
#include <numeric>
#include <ostream>
#include <vector>

#include <experimental/optional>

#include "dreal/solver/config.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {
// Given a dynamic system `xᵢ = fᵢ(x)`, checks that a given candidate
// function `V` is a Lyapunov function of the system within a ball
// bounded by `ball_lb` and `ball_ub`, that is, `ball_lb ≤ ∑xᵢ² ≤
// ball_ub`. It uses `delta` to check its delta-satisfiability when it
// looks for a counterexample.
std::experimental::optional<Box> CheckLyapunov(const std::vector<Variable>& x,
                                               const std::vector<Expression>& f,
                                               const Expression& V,
                                               double ball_lb, double ball_ub,
                                               Config config);

/// Given a partially specified candidate function `V`, synthesizes a
/// Lyapunov function of a dynamic system `xᵢ = fᵢ(x)` within a ball
/// bounded by `ball_lb` and `ball_ub`. The candidate function `V(c,
/// x)` should satisfy the following conditions:
///
///  - ∃c.∀x. x ∈ ball → (V(c, x) ≥ 0 ∧ V̇(c, x) ≤ 0)
///  - ∃c.    V(c, 0) = 0
///  - ∃c.    c_lb ≤ c ≤ c_ub
std::experimental::optional<Box> SynthesizeLyapunov(
    const std::vector<Variable>& x, const std::vector<Expression>& f,
    const Expression& V, double ball_lb, double ball_ub, double c_lb,
    double c_ub, Config config);
}  // namespace dreal
