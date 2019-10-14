#include "dreal/optimization/nlopt_optimizer.h"

#include <cmath>
#include <iostream>
#include <vector>

#include <gtest/gtest.h>

namespace dreal {
namespace {

using std::sqrt;
using std::vector;

class NloptOptimizerTest : public ::testing::Test {
 protected:
  const Variable x1_{"x1"};
  const Variable x2_{"x2"};
  const Variable x3_{"x3"};
  Box b_{{x1_, x2_}};
};

// From the example in
// https://nlopt.readthedocs.io/en/latest/NLopt_Tutorial.
TEST_F(NloptOptimizerTest, NloptTutorial) {
  Config config;
  const double delta{1e-8};
  config.mutable_precision() = delta;
  b_[x2_] = Box::Interval(1e-6, DBL_MAX);
  NloptOptimizer opt(nlopt::algorithm::LD_SLSQP, b_, config);
  opt.SetMinObjective(sqrt(x2_));
  opt.AddConstraint(x2_ >= pow(2 * x1_ + 0, 3));
  opt.AddConstraint(x2_ > pow(-x1_ + 1, 3));

  vector<double> sol{0.5, 3.0};
  double v{0.0};
  const nlopt::result result{opt.Optimize(&sol, &v)};

  EXPECT_GT(result, 0);
  EXPECT_NEAR(sol[0], 1.0 / 3.0, delta);
  EXPECT_NEAR(sol[1], 8.0 / 27.0, delta);
  EXPECT_NEAR(v, sqrt(8.0 / 27.0), delta);
}

TEST_F(NloptOptimizerTest, UnconstrainedRosenbrock) {
  // See http://www.okstate.edu/sas/v8/saspdf/iml/chap11.pdf.
  Config config;
  const double delta{1e-8};
  config.mutable_precision() = delta;
  config.mutable_nlopt_ftol_abs() = delta / 10;
  config.mutable_nlopt_ftol_rel() = delta / 10;
  NloptOptimizer opt(nlopt::algorithm::LD_SLSQP, b_, config);
  opt.SetMinObjective(0.5 * (100 * pow(x2_ - x1_ * x1_, 2) + pow(1 - x1_, 2)));

  vector<double> sol{-1.2, 1.0};
  double v{0.0};
  const nlopt::result result{opt.Optimize(&sol, &v)};

  EXPECT_GT(result, 0);
  EXPECT_NEAR(sol[0], 1.0, 100 * delta);
  EXPECT_NEAR(sol[1], 1.0, 100 * delta);
  EXPECT_NEAR(v, 0.0, delta);
}

TEST_F(NloptOptimizerTest, ConstrainedBetts) {
  // See http://www.okstate.edu/sas/v8/saspdf/iml/chap11.pdf.
  Config config;
  const double delta{1e-8};
  config.mutable_precision() = delta;
  config.mutable_nlopt_ftol_abs() = delta / 10;
  config.mutable_nlopt_ftol_rel() = delta / 10;
  b_[x1_] = Box::Interval(2.0, 50.0);
  b_[x2_] = Box::Interval(-50.0, 50.0);
  NloptOptimizer opt(nlopt::algorithm::LD_SLSQP, b_, config);
  opt.SetMinObjective(0.01 * x1_ * x1_ + x2_ * x2_ - 100);
  opt.AddConstraint(10.0 <= 10 * x1_ - x2_);

  vector<double> sol{2.05, 0.01};
  double v{0.0};
  const nlopt::result result{opt.Optimize(&sol, &v)};

  EXPECT_GT(result, 0);
  EXPECT_NEAR(sol[0], 2.0, 100 * delta);
  EXPECT_NEAR(sol[1], 0.0, 100 * delta);
  EXPECT_NEAR(v, -99.96, delta);
}

TEST_F(NloptOptimizerTest, EqualityConstraint) {
  // See http://mat.gsia.cmu.edu/classes/QUANT/NOTES/chap4.pdf
  Config config;
  const double delta{1e-4};
  config.mutable_precision() = delta;
  Box b{{x1_, x2_, x3_}};
  b[x1_] = Box::Interval(1.0, 1.0);
  NloptOptimizer opt(nlopt::algorithm::LD_SLSQP, b, config);
  opt.SetMinObjective(x1_ + x2_ + x3_ * x3_);
  opt.AddConstraint(x1_ * x1_ + x2_ * x2_ == 1.0);

  vector<double> sol{1, 0.5, 0.1};
  double v{0.0};
  const nlopt::result result{opt.Optimize(&sol, &v)};

  EXPECT_GT(result, 0);
  EXPECT_NEAR(sol[0], 1.0, delta);
  EXPECT_NEAR(sol[1], 0.0, delta);
  EXPECT_NEAR(sol[2], 0.0, delta);
  EXPECT_NEAR(v, 1, delta);
}

}  // namespace
}  // namespace dreal
