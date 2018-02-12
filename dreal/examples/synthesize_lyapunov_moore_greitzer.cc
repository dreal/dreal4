#include "dreal/examples/control.h"

#include <iostream>
#include <vector>

namespace dreal {
namespace {

using std::cout;
using std::endl;
using std::vector;

void synthesize_lyapunov_moore_greitzer() {
  // Moore-Greitzer Jet Engine
  const Variable x1{"x1"};
  const Variable x2{"x2"};

  // Derivatives
  const Expression x1_dot{-x2 - 1.5 * x1 * x1 - 0.5 * x1 * x1 * x1};
  const Expression x2_dot{3 * x1 - x2};

  Expression V = 0.0;

  const vector<Expression> monomials{x1 * x1, x1 * x2, x2 * x2, x1, x2};

  int k = 0;
  for (size_t idx1 = 0; idx1 < monomials.size(); ++idx1) {
    for (size_t idx2 = idx1; idx2 < monomials.size(); ++idx2) {
      const Variable q_k{"q_" + std::to_string(++k)};
      V += monomials[idx1] * monomials[idx2] * q_k;
    }
  }

  // Synthesize one.
  Config config;
  config.mutable_precision() = 0.01;
  config.mutable_use_polytope_in_forall() = true;
  config.mutable_use_local_optimization() = true;

  // clang-format off
  const auto result = SynthesizeLyapunov(
      {x1, x2},
      {x1_dot, x2_dot},
      V,
      0.3 /* lb of ball */, 0.5 /* ub of ball */,
      -10.0 /* lb of q_i */, 10.0 /* ub of q_i */,
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

int main() { dreal::synthesize_lyapunov_moore_greitzer(); }
