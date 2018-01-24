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
  config.mutable_precision() = 0.0001;
  config.mutable_use_polytope_in_forall() = true;
  config.mutable_use_local_optimization() = true;

  // Check that the solution in the paper is indeed a solution.
  // clang-format off
  CheckLyapunov({x1, x2},
                {x2, -sin(x1) - x2},
                100.0 * x1 * x1 + 92.0 * x2 * x2 + 48 * x1 * x2,
                0.001, 1.0, /* lb&ub of ball */
                config);
  // clang-format on

  // Synthesize one.
  // clang-format off
  Expression V{c1 * x1 * x1 + c2 * x2 * x2 + c3 * x1 * x2};
  const auto result =
    SynthesizeLyapunov({x1, x2},
                       {x2, -sin(x1) - x2},
                       V,
                       0.0001, 1.0, /* lb&ub of ball */
                       0.1, 1.0,    /* lb&ub of c_i */
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
