#include "dreal/examples/control.h"

#include <iostream>
#include <vector>

#include "dreal/util/logging.h"

namespace dreal {
namespace {

using std::cout;
using std::endl;
using std::vector;

void synthesize_lyapunov_damped_mathieu() {
  // From Section 5.3 of the following paper:
  //
  // James Kapinski, Jyotirmoy V. Deshmukh, Sriram Sankaranarayanan,
  // and Nikos Arechiga. 2014. Simulation-guided lyapunov analysis for
  // hybrid dynamical systems. In Proceedings of the 17th
  // international conference on Hybrid systems: computation and
  // control (HSCC '14). ACM, New York, NY, USA,
  // 133-142. DOI=http://dx.doi.org/10.1145/2562059.2562139
  //
  // Damped Mathieu System.
  //           ẋ₁ = x₂
  //           ẋ₂ = -x₂ - (2 + sin(t))x₁
  //           t' = 1
  // Candidate V  = c₁x₁² + c₂x₂² + c₃x₁x₂.
  const Variable x1{"x1"};
  const Variable x2{"x2"};
  const Variable t{"t"};

  Config config;
  config.mutable_precision() = 0.05;
  config.mutable_use_polytope_in_forall() = true;
  config.mutable_use_local_optimization() = true;

  // Synthesize one.
  Expression V = 0.0;
  const vector<Expression> monomials{x1, x2};
  double scaling_factor = 50.0;
  int k = 0;
  for (size_t idx1 = 0; idx1 < monomials.size(); ++idx1) {
    for (size_t idx2 = idx1; idx2 < monomials.size(); ++idx2) {
      const Variable c_k{"c_" + std::to_string(++k)};
      V += monomials[idx1] * monomials[idx2] * scaling_factor * c_k;
    }
  }

  // clang-format off
  const auto result =
    SynthesizeLyapunov({x1, x2}, t,
                       {x2, -x2 - (2 + sin(t)) * x1, 1},
                       V,
                       0.1, 1.0, /* lb&ub of ball */
                       45 / scaling_factor, 98 / scaling_factor,
                       /* lb&ub of c_i */
                       0.1, 1.0, /* lb&ub of time */
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
