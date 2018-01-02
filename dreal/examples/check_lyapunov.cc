#include <cmath>
#include <numeric>
#include <ostream>
#include <vector>
#include <experimental/optional>

#include "dreal/api/api.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/assert.h"
#include "dreal/util/box.h"

namespace dreal {
namespace {

using std::accumulate;
using std::cout;
using std::endl;
using std::experimental::optional;
using std::vector;

// Given a dynamic system `xᵢ = fᵢ(x)`, checks that a given candidate
// function `V` is a Lyapunov function of the system within a ball
// bounded by `ball_lb` and `ball_ub`, that is, `ball_lb ≤ ∑xᵢ² ≤
// ball_ub`. It uses `delta` to check its delta-satisfiability when it
// looks for a counterexample.
void CheckLyapunov(const vector<Variable>& x, const vector<Expression>& f,
                   const Expression& V, const double ball_lb,
                   const double ball_ub, const double delta) {
  DREAL_ASSERT(x.size() == f.size());
  DREAL_ASSERT(ball_lb > 0.0);
  DREAL_ASSERT(ball_ub > 0.0);
  DREAL_ASSERT(ball_ub > ball_lb);
  DREAL_ASSERT(delta > 0.0);

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

void check_lyapunov_example1() {
  // ẋ₁ = x₂
  // ẋ₂ = -sin(x₁)
  // V  = (1 - cos(x₁)) + 0.5x₂²
  const Variable x1{"x1"};
  const Variable x2{"x2"};
  // clang-format off
  CheckLyapunov({x1, x2},
                {x2, -sin(x1)},
                (1 - cos(x1)) + 0.5 * x2 * x2,
                0.001, M_PI * M_PI,
                1e-5);
  // clang-format on
}

void check_lyapunov_example2() {
  // ẋ₁ = -x₂ - x₁³
  // ẋ₂ =  x₁ - x₂³
  // V  = x₁² + x₂²
  const Variable x1{"x1"};
  const Variable x2{"x2"};
  // clang-format off
  CheckLyapunov({x1, x2},
                {-x2 - pow(x1, 3),
                  x1 - pow(x2, 3)},
                x1 * x1 + x2 * x2,
                0.1, 0.5,
                1e-5);
  // clang-format on
}
}  // namespace
}  // namespace dreal

int main() {
  dreal::check_lyapunov_example1();
  dreal::check_lyapunov_example2();
}
