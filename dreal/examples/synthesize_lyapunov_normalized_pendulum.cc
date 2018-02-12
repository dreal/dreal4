#include "dreal/examples/control.h"

#include <iostream>

namespace dreal {
namespace {

using std::cout;
using std::endl;

void synthesize_lyapunov_normalized_pendulum() {
  // Section 5.1. Example 1: Normalized Pendulum
  //           ẋ₁ = x₂
  //           ẋ₂ = -sin(x₁) - x₂
  // Candidate V  = c₁x₁² + c₂x₂² + c₃x₁x₂.
  const Variable x1{"x1"};
  const Variable x2{"x2"};

  const Variable c1{"c1"};
  const Variable c2{"c2"};
  const Variable c3{"c3"};

  Config config;
  config.mutable_precision() = 0.05;
  config.mutable_use_polytope_in_forall() = true;
  config.mutable_use_local_optimization() = true;

  config.mutable_nlopt_ftol_rel() = 1e-6;
  config.mutable_nlopt_ftol_abs() = 1e-6;
  config.mutable_nlopt_maxeval() = 30;
  config.mutable_nlopt_maxtime() = 0.01;

  // Check that the solution in the paper is indeed a solution.
  // clang-format off
  CheckLyapunov({x1, x2},
                {x2, -sin(x1) - x2},
                100.0 * x1 * x1 + 92.0 * x2 * x2 + 48 * x1 * x2,
                0.001, 1.0, /* lb&ub of ball */
                config);
  // clang-format on

  // Synthesize one.
  double scaling_factor = 50.0;
  Expression V{c1 * scaling_factor * x1 * x1 + c2 * scaling_factor * x2 * x2 +
               c3 * scaling_factor * x1 * x2};
  // clang-format off
  const auto result =
    SynthesizeLyapunov({x1, x2},
                       {x2, -sin(x1) - x2},
                       V,
                       /* lb&ub of ball */
                       0.1, 1.0,
                       /* lb&ub of c_i */
                       0.1 / scaling_factor, 100.0 / scaling_factor,
                       config);
  // clang-format on
  if (result) {
    cout << "Found:" << endl << *result << endl;
    for (const Variable& var : result->variables()) {
      V = V.Substitute(var, (*result)[var].mid());
    }
    cout << "V = " << V << endl;
  } else {
    cout << "Not found." << endl;
  }
}
}  // namespace
}  // namespace dreal

int main() {
  dreal::synthesize_lyapunov_normalized_pendulum();
}
