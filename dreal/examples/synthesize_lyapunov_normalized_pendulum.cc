#include "dreal/examples/control.h"

#include <iostream>

namespace dreal {
namespace {

using std::cout;
using std::endl;

void synthesize_lyapunov_normalized_pendulum() {
  // From Section 5.1 of the following paper:
  //
  // James Kapinski, Jyotirmoy V. Deshmukh, Sriram Sankaranarayanan,
  // and Nikos Arechiga. 2014. Simulation-guided lyapunov analysis for
  // hybrid dynamical systems. In Proceedings of the 17th
  // international conference on Hybrid systems: computation and
  // control (HSCC '14). ACM, New York, NY, USA,
  // 133-142. DOI=http://dx.doi.org/10.1145/2562059.2562139
  //
  // Normalized Pendulum
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

int main() { dreal::synthesize_lyapunov_normalized_pendulum(); }
