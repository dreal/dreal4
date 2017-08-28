#include "dreal/contractor/contractor_ibex_fwdbwd.h"

#include <iostream>

#include <gtest/gtest.h>

#include "dreal/contractor/contractor_status.h"
#include "dreal/util/box.h"
#include "dreal/util/symbolic.h"

namespace dreal {
namespace {

class ContractorIbexFwdbwdTest : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};
  const Variables vars_{{x_, y_, z_}};
  Box box_{vars_};
};

TEST_F(ContractorIbexFwdbwdTest, Sat) {
  const Formula f{cos(x_) == sin(y_)};
  box_[x_] = Box::Interval(0.0, 3.14 / 2);
  box_[y_] = Box::Interval(0.2, 0.3);
  box_[z_] = Box::Interval(0.0, 1.0);
  ContractorStatus cs{box_};
  const ContractorIbexFwdbwd ctc{f, box_};

  // Inputs
  EXPECT_TRUE(ctc.input()[0]);
  EXPECT_TRUE(ctc.input()[1]);
  EXPECT_FALSE(ctc.input()[2]);

  // Before pruning, the box is not empty.
  EXPECT_FALSE(cs.box().empty());

  ctc.Prune(&cs);

  // After pruning, the box is still not empty.
  EXPECT_FALSE(cs.box().empty());

  // x : [1.2708, 1.3708]
  // y : [0.2, 0.3]
  // z : [0.0, 1.0]
  EXPECT_TRUE(cs.box()[x_].is_subset(Box::Interval(1.270, 1.371)));
  EXPECT_EQ(cs.box()[y_], Box::Interval(0.2, 0.3));
  EXPECT_EQ(cs.box()[z_], Box::Interval(0.0, 1.0));

  // Outputs. Only x-dimension is changed.
  EXPECT_TRUE(cs.output()[0]);
  EXPECT_FALSE(cs.output()[1]);
  EXPECT_FALSE(cs.output()[2]);
}

TEST_F(ContractorIbexFwdbwdTest, Unsat) {
  const Formula f{sin(x_) == y_};
  box_[x_] = Box::Interval(0.1, 0.2);
  box_[y_] = Box::Interval(0.2, 0.3);
  box_[z_] = Box::Interval(0.0, 1.0);
  ContractorStatus cs{box_};
  const ContractorIbexFwdbwd ctc{f, box_};

  // Inputs: only x and y.
  EXPECT_TRUE(ctc.input()[0]);
  EXPECT_TRUE(ctc.input()[1]);
  EXPECT_FALSE(ctc.input()[2]);

  // Before pruning, the box is not empty.
  EXPECT_FALSE(cs.box().empty());

  ctc.Prune(&cs);

  // After pruning, the box is empty.
  EXPECT_TRUE(cs.box().empty());

  // Outputs. All dimensions are changed.
  EXPECT_TRUE(cs.output()[0]);
  EXPECT_TRUE(cs.output()[1]);
  EXPECT_TRUE(cs.output()[2]);
}
}  // namespace
}  // namespace dreal
