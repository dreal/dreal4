#include "dreal/examples/control.h"

#include <iostream>
#include <vector>

namespace dreal {
namespace {

using std::cout;
using std::endl;
using std::vector;

void synthesize_lyapunov_power_train() {
  // Section 5.5. Example 5: Power Control System.
  const Variable p{"p"};
  const Variable r{"r"};
  const Variable p_est{"p_est"};
  const Variable i{"i"};

  // PTC parameters
  const double c1{0.41328};
  const double c2{200.0};
  const double c3{-0.366};
  const double c4{0.08979};
  const double c5{-0.0337};
  const double c6{0.0001};
  const double c11{1.0};
  const double c13{0.9};
  const double c14{0.4};
  const double c15{0.4};
  const double c16{1.0};
  const double u1{23.0829};

  // Derivatives
  const Expression p_dot{
      c1 * (2 * u1 * sqrt(p / c11 - pow(p / c11, 2)) -
            (c3 + c4 * c2 * p + c5 * c2 * p * p + c6 * c2 * c2 * p))};
  const Expression r_dot{
      4 * ((c3 + c4 * c2 * p + c5 * c2 * p * p + c6 * c2 * c2 * p) /
               (c13 *
                (c3 + c4 * c2 * p_est + c5 * c2 * p_est * p_est +
                 c6 * c2 * c2 * p_est) *
                (1 + i + c14 * (r - c16))) -
           r)};
  const Expression p_est_dot{
      c1 * (2 * u1 * sqrt(p / c11 - pow(p / c11, 2)) -
            c13 * (c3 + c4 * c2 * p_est + c5 * c2 * p_est * p_est +
                   c6 * c2 * c2 * p_est))};
  const Expression i_dot{c15 * (r - c16)};

  Expression V = 0.0;

  const vector<Expression> monomials{
      p * p,         p * r,     p * p_est, p * i, r * r, r * p_est, r * i,
      p_est * p_est, p_est * i, i * i,     p,     r,     p_est,     i};

  int k = 0;
  const double scaling_factor{100.0};
  for (size_t idx1 = 0; idx1 < monomials.size(); ++idx1) {
    for (size_t idx2 = idx1; idx2 < monomials.size(); ++idx2) {
      const Variable q_k{"q_" + std::to_string(++k)};
      V += monomials[idx1] * monomials[idx2] * scaling_factor * q_k;
    }
  }

  // Synthesize one.
  Config config;
  config.mutable_precision() = 0.05;
  config.mutable_use_polytope_in_forall() = true;
  config.mutable_use_local_optimization() = true;

  // clang-format off
  const auto result =
      SynthesizeLyapunov({p, r, p_est, i},
                         {p_dot, r_dot, p_est_dot, i_dot},
                         V,
                         0.1 /* lb of ball */, 1.0 /* ub of ball */,
                         -100.0 / scaling_factor /* lb of q_i */,
                         100.0 / scaling_factor/* ub of q_i */,
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

int main() { dreal::synthesize_lyapunov_power_train(); }
