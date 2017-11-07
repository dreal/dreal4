#include <cmath>
#include <numeric>
#include <ostream>
#include <vector>
#include <experimental/optional>

#include "dreal/api/api.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

using std::accumulate;
using std::cout;
using std::endl;
using std::experimental::optional;
using std::vector;

namespace dreal {
namespace {

// Given a dynamic system `xᵢ = fᵢ(x)`, checks that a given candidate
// function `V` is a Lyapunov function of the system within a ball
// bounded by `ball_lb` and `ball_ub`, that is, `ball_lb ≤ ∑xᵢ² ≤
// ball_ub`. It uses `delta` to check its delta-satisfiability when it
// looks for a counterexample.
void CheckLyapunov(const vector<Variable>& x, const vector<Expression>& f,
                   const Expression& V, const double ball_lb,
                   const double ball_ub, const double delta) {
  assert(x.size() == f.size());
  assert(ball_lb > 0.0);
  assert(ball_ub > 0.0);
  assert(ball_ub > ball_lb);
  assert(delta > 0.0);

  // ball = ∑ xᵢ².
  const Expression ball =
      accumulate(x.begin(), x.end(), Expression::Zero(),
                 [](const Expression& result, const Variable& x_i) {
                   return result + (x_i * x_i);
                 });
  // lie_derivative_of_V = ∑ fᵢ*∂V/∂xᵢ.
  Expression lie_derivative_of_V = 0.0;
  for (size_t i = 0; i < x.size(); i++) {
    lie_derivative_of_V += f[i] * V.Differentiate(x[i]);
  }

  const Formula ball_in_bound = (ball_lb <= ball) && (ball <= ball_ub);
  const Formula condition = (imply(ball_in_bound, V >= 0) &&
                             imply(ball_in_bound, lie_derivative_of_V <= 0));
  const auto result = CheckSatisfiability(!condition, delta);

  cout << "=======================================" << endl;
  if (result) {
    cout << "The function\n"
         << "\tV = " << V << "\n"
         << "is not a Lyapunov function for the system defined by" << endl;
    cout << "\tf = [";
    for (const Expression& f_i : f) {
      cout << f_i << ";";
    }
    cout << "]" << endl;
    cout << "because a counterexample has been found.\n";
    cout << *result << endl;
  } else {
    cout << "The Lyapunov function\n"
         << "\tV = " << V << "\n"
         << "is valid for the system defined by" << endl;
    cout << "\tf = [";
    for (const Expression& f_i : f) {
      cout << f_i << ";";
    }
    cout << "]" << endl;
  }
}

/// Given a partially specified candidate function `V`, synthesizes a
/// Lyapunov function of a dynamic system `xᵢ = fᵢ(x)` within a ball
/// bounded by `ball_lb` and `ball_ub`. The candidate function `V(c,
/// x)` should satisfy the following conditions:
///
///  - ∃c.∀x. x ∈ ball → (V(c, x) ≥ 0 ∧ V̇(c, x) ≤ 0)
///  - ∃c.    V(c, 0) = 0
///  - ∃c.    c_lb ≤ c ≤ c_ub
///
void SynthesizeLyapunov(const vector<Variable>& x, const vector<Expression>& f,
                        const Expression& V, const double ball_lb,
                        const double ball_ub, const double c_lb,
                        const double c_ub, const double delta) {
  // ∃c.∀x. x ∈ ball → (V(c, x) ≥ 0 ∧ V̇(c, x) ≤ 0)
  // ball = ∑ xᵢ².
  const Expression ball =
      accumulate(x.begin(), x.end(), Expression::Zero(),
                 [](const Expression& result, const Variable& x_i) {
                   return result + (x_i * x_i);
                 });
  // lie_derivative_of_V = ∑ fᵢ*∂V/∂xᵢ.
  Expression lie_derivative_of_V = 0.0;
  for (size_t i = 0; i < x.size(); i++) {
    lie_derivative_of_V += f[i] * V.Differentiate(x[i]);
  }

  // Add: ∀x. x ∈ Ball → (V(c, x) ≥  0 V̇(c, x) ≤ 0)
  const Formula ball_in_bound = (ball_lb <= ball) && (ball <= ball_ub);
  const Formula nested_condition =
      imply(ball_in_bound, V > 0 && lie_derivative_of_V <= 0);
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
  const auto result = CheckSatisfiability(condition, delta);

  // Double check the solution by calling CheckLyapunov.
  if (result) {
    // We found a candidate!
    const Box& solution{*result};
    ExpressionSubstitution subst_solution;
    for (const Variable& v : solution.variables()) {
      subst_solution.emplace(v, solution[v].mid());
    }
    CheckLyapunov(x, f, V.Substitute(subst_solution), ball_lb, ball_ub, delta);
  } else {
    cout << "Failed to synthesize a Lyapunov function." << endl;
  }
}

void synthesize_lyapunov_example1() {
  //           ẋ₁ = -x₂ - x₁³
  //           ẋ₂ =  x₁ - x₂³
  // Candidate V  = c₁x₁² + c₂x₂² + c₃x₁x₂ + c₄.
  const Variable x1{"x1"};
  const Variable x2{"x2"};

  const Variable c1{"c1"};
  const Variable c2{"c2"};
  const Variable c3{"c3"};
  const Variable c4{"c4"};

  // clang-format off
  SynthesizeLyapunov({x1, x2},
                     {-x2 - pow(x1, 3),
                       x1 - pow(x2, 3)},
                     c1 * x1 * x1 + c2 * x2 * x2 + c3 * x1 * x2 + c4,
                     0.1, 0.2, /* lb&ub of ball */
                     0, 1,    /* lb&ub of c_i */
                     0.001);
  // clang-format on
}
}  // namespace
}  // namespace dreal

int main() { dreal::synthesize_lyapunov_example1(); }
