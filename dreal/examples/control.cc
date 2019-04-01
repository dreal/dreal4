#include "dreal/examples/control.h"

#include <numeric>
#include <utility>

#include "dreal/api/api.h"
#include "dreal/util/assert.h"
#include "dreal/util/nnfizer.h"

namespace dreal {

using std::accumulate;
using std::move;
using std::vector;

optional<Box> CheckLyapunov(const vector<Variable>& x,
                            const vector<Expression>& f, const Expression& V,
                            const double ball_lb, const double ball_ub,
                            Config config) {
  DREAL_ASSERT(x.size() == f.size());
  DREAL_ASSERT(ball_lb > 0.0);
  DREAL_ASSERT(ball_ub > 0.0);
  DREAL_ASSERT(ball_ub > ball_lb);
  DREAL_ASSERT(config.precision() > 0.0);

  // ball = ∑xᵢ².
  const Expression ball =
      accumulate(x.begin(), x.end(), Expression::Zero(),
                 [](const Expression& result, const Variable& x_i) {
                   return result + (x_i * x_i);
                 });

  // lie_derivative_of_V = ∑fᵢ*∂V/∂xᵢ.
  Expression lie_derivative_of_V = 0.0;  // NOLINT
  for (size_t i = 0; i < x.size(); i++) {
    lie_derivative_of_V += f[i] * V.Differentiate(x[i]);
  }

  // Note that we use (ball_lb)² and (ball_ub)² to avoid sqrt(ball).
  const Formula ball_in_bound =
      (ball_lb * ball_lb <= ball) && (ball <= ball_ub * ball_ub);
  const Formula condition = (imply(ball_in_bound, V >= 0) &&
                             imply(ball_in_bound, lie_derivative_of_V <= 0));
  return CheckSatisfiability(!condition, move(config));
}

optional<Box> CheckLyapunov(const vector<Variable>& x, const Variable& t,
                            const vector<Expression>& f, const Expression& V,
                            const double ball_lb, const double ball_ub,
                            const double t_lb, const double t_ub,
                            Config config) {
  DREAL_ASSERT(x.size() + 1 == f.size());
  DREAL_ASSERT(ball_lb > 0.0);
  DREAL_ASSERT(ball_ub > 0.0);
  DREAL_ASSERT(ball_ub > ball_lb);
  DREAL_ASSERT(config.precision() > 0.0);

  // ball = ∑xᵢ².
  const Expression ball =
      accumulate(x.begin(), x.end(), Expression::Zero(),
                 [](const Expression& result, const Variable& x_i) {
                   return result + (x_i * x_i);
                 });

  // lie_derivative_of_V = ∑fᵢ*∂V/∂xᵢ.
  Expression lie_derivative_of_V = 0.0;  // NOLINT
  for (size_t i = 0; i < x.size(); i++) {
    lie_derivative_of_V += f[i] * V.Differentiate(x[i]);
  }

  // Note that we use (ball_lb)² and (ball_ub)² to avoid sqrt(ball).
  const Formula ball_in_bound =
      (ball_lb * ball_lb <= ball) && (ball <= ball_ub * ball_ub);
  const Formula condition =
      imply(t_lb <= t && t <= t_ub,
            imply(ball_in_bound, V >= 0) &&
                imply(ball_in_bound, lie_derivative_of_V <= 0));
  return CheckSatisfiability(!condition, move(config));
}

optional<Box> SynthesizeLyapunov(const vector<Variable>& x,
                                 const vector<Expression>& f,
                                 const Expression& V, const double ball_lb,
                                 const double ball_ub, const double c_lb,
                                 const double c_ub, Config config) {
  // ∃c.∀x. x ∈ ball → (V(c, x) > 0 ∧ V̇(c, x) < 0)
  // ball = ∑xᵢ².
  const Expression ball =
      accumulate(x.begin(), x.end(), Expression::Zero(),
                 [](const Expression& result, const Variable& x_i) {
                   return result + (x_i * x_i);
                 });
  // lie_derivative_of_V = ∑fᵢ*∂V/∂xᵢ.
  Expression lie_derivative_of_V = 0.0;  // NOLINT
  for (size_t i = 0; i < x.size(); i++) {
    lie_derivative_of_V += f[i] * V.Differentiate(x[i]);
  }

  // Add: ∀x. x ∈ Ball → (V(c, x) > 0 ∧ V̇(c, x) < 0)
  // Note that we use (ball_lb)² and (ball_ub)² to avoid sqrt(ball).
  const Formula ball_in_bound =
      (ball_lb * ball_lb <= ball) && (ball <= ball_ub * ball_ub);

  // const Formula nested_condition = imply(
  //     ball_in_bound, (V > config.precision() * 10) &&
  //                        (lie_derivative_of_V < -config.precision() * 10));

  const Formula nested_condition =
      imply(ball_in_bound, (V > 0.0) && (lie_derivative_of_V < -0.0));

  Variables forall_variables;
  forall_variables.insert(x.begin(), x.end());
  Formula condition = forall(forall_variables, nested_condition);

  // Add: c ∈ [c_lb, c_ub].
  for (const Variable& c : V.GetVariables()) {
    if (!forall_variables.include(c)) {
      condition = condition && (c_lb <= c) && (c <= c_ub);
    }
  }

  // Add: V(c, 0) = 0
  ExpressionSubstitution subst_zero;
  for (const Variable& x_i : x) {
    subst_zero.emplace(x_i, 0.0);
  }
  condition = condition && (V.Substitute(subst_zero) == 0.0);

  // Find c, the coefficients of V.
  std::cerr << condition << std::endl;
  const auto result = CheckSatisfiability(condition, config);

  // Double check the solution by calling CheckLyapunov.
  if (result) {
    // We found a candidate!
    const Box& solution{*result};
    ExpressionSubstitution subst_solution;
    for (const Variable& v : solution.variables()) {
      subst_solution.emplace(v, solution[v].mid());
    }
    // Double check, using a smaller delta!
    config.mutable_precision() = config.precision() * 0.1;
    const Expression found_V = V.Substitute(subst_solution);
    std::cout << "Found V = " << found_V << std::endl;
    const auto confirm =
        CheckLyapunov(x, f, found_V, ball_lb, ball_ub, move(config));
    if (!confirm) {
      std::cout << "Confirmed! Found V = " << found_V << std::endl;
      return solution;
    } else {
      std::cout << "CE Found = " << *confirm << std::endl;
      return {};
    }
  } else {
    std::cout << "Failed to find V." << std::endl;
    return {};
  }
}

optional<Box> SynthesizeLyapunov(const vector<Variable>& x, const Variable& t,
                                 const vector<Expression>& f,
                                 const Expression& V, const double ball_lb,
                                 const double ball_ub, const double c_lb,
                                 const double c_ub, const double t_lb,
                                 const double t_ub, Config config) {
  // ∃c.∀x,t. (x ∈ ball ∧ t ∈ [t_lb, t_ub) → (V(c, x) ≥ 0 ∧ V̇(c, x) ≤ 0)
  // ball = ∑xᵢ².
  const Expression ball =
      accumulate(x.begin(), x.end(), Expression::Zero(),
                 [](const Expression& result, const Variable& x_i) {
                   return result + (x_i * x_i);
                 });
  // lie_derivative_of_V = ∑fᵢ*∂V/∂xᵢ.
  Expression lie_derivative_of_V = 0.0;  // NOLINT
  for (size_t i = 0; i < x.size(); i++) {
    lie_derivative_of_V += f[i] * V.Differentiate(x[i]);
  }

  // Add: ∀x. (x ∈ Ball ∧ t ∈ [t_lb, t_ub)) → (V(c, x) ≥  0 V̇(c, x) ≤ 0)
  // Note that we use (ball_lb)² and (ball_ub)² to avoid sqrt(ball).
  const Formula ball_in_bound =
      (ball_lb * ball_lb <= ball) && (ball <= ball_ub * ball_ub);
  const Formula t_in_bound = (t_lb <= t) && (t <= t_ub);
  const Formula nested_condition =
      imply(ball_in_bound && t_in_bound, V > 0 && lie_derivative_of_V < 0);
  Variables forall_variables;
  forall_variables.insert(x.begin(), x.end());
  forall_variables.insert(t);
  Formula condition = forall(forall_variables, nested_condition);

  // Add: c ∈ [c_lb, c_ub].
  for (const Variable& c : V.GetVariables()) {
    if (!forall_variables.include(c)) {
      condition = condition && (c_lb <= c) && (c <= c_ub);
    }
  }

  // Add: V(c, 0) = 0
  ExpressionSubstitution subst_zero;
  for (const Variable& x_i : x) {
    subst_zero.emplace(x_i, 0.0);
  }
  condition = condition && (V.Substitute(subst_zero) == 0.0);

  // Find c, the coefficients of V.
  std::cerr << condition << std::endl;
  const auto result = CheckSatisfiability(condition, config);

  // Double check the solution by calling CheckLyapunov.
  if (result) {
    // We found a candidate!
    const Box& solution{*result};
    ExpressionSubstitution subst_solution;
    for (const Variable& v : solution.variables()) {
      subst_solution.emplace(v, solution[v].mid());
    }
    // Double check, using a smaller delta!
    config.mutable_precision() = config.precision() * 0.1;
    const Expression found_V = V.Substitute(subst_solution);
    std::cout << "Found V = " << found_V << std::endl;
    const auto confirm = CheckLyapunov(x, t, f, found_V, ball_lb, ball_ub, t_lb,
                                       t_ub, move(config));
    if (!confirm) {
      std::cout << "Confirmed! Found V = " << found_V << std::endl;
      return solution;
    } else {
      std::cout << "CE Found = " << *confirm << std::endl;
      return {};
    }
  } else {
    std::cout << "Failed to find V." << std::endl;
    return {};
  }
}

}  // namespace dreal
