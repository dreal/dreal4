#include <cmath>
#include <iostream>
#include <vector>

#include <nlopt.hpp>

using std::cerr;
using std::cout;
using std::endl;
using std::vector;

namespace dreal {
namespace {

double obj(unsigned, const double* x, double*, void*) {
  double const ret = sin(x[0]) * cos(x[1]);
  cerr << "sin(" << x[0] << ")"
       << " * "
       << "cos(" << x[1] << ") = " << ret << endl;
  return ret;
}

int Main() {
  nlopt::opt opt(nlopt::LN_COBYLA, 2);

  // lower bound
  //    0 <= x[0]
  //    0 <= x[1]
  vector<double> lb(2);
  lb[0] = 0;
  lb[1] = 0;
  opt.set_lower_bounds(lb);

  // upper bound
  //    x[0] <= 10
  //    x[1] <= 10
  vector<double> ub(2);
  ub[0] = 10;
  ub[1] = 10;
  opt.set_upper_bounds(ub);

  // set objective function
  opt.set_min_objective(obj, nullptr);

  // set tollerance
  opt.set_xtol_abs(0.0001);

  // set initial point
  //    init[0] = 5.0
  //    init[1] = 5.0
  vector<double> init;
  init.push_back(5.0);
  init.push_back(5.0);

  // Call optimization
  vector<double> output = opt.optimize(init);

  // Print result
  cout << "output: x0 = " << output[0] << endl;
  cout << "output: x1 = " << output[1] << endl;
  return 0;
}

}  // namespace
}  // namespace dreal

int main() { return dreal::Main(); }
