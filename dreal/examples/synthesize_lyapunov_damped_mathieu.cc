#include "dreal/examples/control.h"

#include <iostream>

namespace dreal {
namespace {

using std::cout;
using std::endl;

void synthesize_lyapunov_damped_mathieu() {
  // Section 5.3. Example 3: Damped Mathieu System.
  //           ẋ₁ = x₂
  //           ẋ₂ = -x₂ - (2 + sin(t))x₁
  //           t' = 1
  // Candidate V  = c₁x₁² + c₂x₂² + c₃x₁x₂.
  const Variable x1{"x1"};
  const Variable x2{"x2"};
  const Variable t{"t"};

  const Variable c1{"c1"};
  const Variable c2{"c2"};
  const Variable c3{"c3"};

  Config config;
  config.mutable_precision() = 0.00001;
  config.mutable_use_polytope_in_forall() = true;
  config.mutable_use_local_optimization() = true;

  // Check that the solution in the paper is indeed a solution.
  const Expression V_candidate{98.0 * x1 * x1 + 55.0 * x2 * x2 +
                               48.0 * x1 * x2};
  // clang-format off
  const auto check_result =
    CheckLyapunov({x1, x2, t},
                  {x2, -x2 - (2 + sin(t)) * x1, 1},
                  V_candidate,
                  0.001, 1.0, /* lb&ub of ball */
                  config);
  // clang-format on
  cout << "V candidate = " << V_candidate;
  if (check_result) {
    cout << " is not a L function." << endl;
  } else {
    cout << " is L function." << endl;
  }
  // Synthesize one.
  Expression V = c1 * x1 * x1 + c2 * x2 * x2 + c3 * x1 * x2;
  // clang-format off
  const auto result =
    SynthesizeLyapunov({x1, x2, t},
                       {x2, -x2 - (2 + sin(t)) * x1, 1},
                       V,
                       0.01, 0.1, /* lb&ub of ball */
                       0.1, 1.0, /* lb&ub of c_i */
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

int main() { dreal::synthesize_lyapunov_damped_mathieu(); }
