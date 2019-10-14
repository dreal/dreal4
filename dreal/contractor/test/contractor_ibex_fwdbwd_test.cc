#include "dreal/contractor/contractor_ibex_fwdbwd.h"

#include <iostream>

#include <gtest/gtest.h>

#include "dreal/contractor/contractor_status.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/interval.h"
#include "dreal/util/string_to_interval.h"

namespace dreal {
namespace {

using std::vector;

class ContractorIbexFwdbwdTest : public ::testing::Test {
 protected:
  const Variable x_{"x", Variable::Type::CONTINUOUS};
  const Variable y_{"y", Variable::Type::CONTINUOUS};
  const Variable z_{"z", Variable::Type::CONTINUOUS};
  const vector<Variable> vars_{{x_, y_, z_}};
  Box box_{vars_};
};

TEST_F(ContractorIbexFwdbwdTest, Sat) {
  const Formula f{cos(x_) == sin(y_)};
  box_[x_] = Box::Interval(0.0, 3.14 / 2);
  box_[y_] = Box::Interval(0.2, 0.3);
  box_[z_] = Box::Interval(0.0, 1.0);
  ContractorStatus cs{box_};
  const ContractorIbexFwdbwd ctc{f, box_, Config{}};

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
  const ContractorIbexFwdbwd ctc{f, box_, Config{}};

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

TEST_F(ContractorIbexFwdbwdTest, TestSmt2Problem20) {
  const Formula f{y_ + z_ == x_};
  ContractorStatus cs{box_};
  const ContractorIbexFwdbwd ctc{f, box_, Config{}};
  Box& box = cs.mutable_box();

  box[x_] = StringToInterval("0.7");
  box[y_] = StringToInterval("0.0647");
  box[z_] = StringToInterval("0.6353");
  ctc.Prune(&cs);

  // After pruning, the box is still not empty.
  EXPECT_FALSE(cs.box().empty());
}

TEST_F(ContractorIbexFwdbwdTest, TestSmt2Problem20Lowlevel) {
  // Given a box,
  //     x = 0.2
  //     y = 0.5
  //     z = 0.7
  //
  // `x + y = z` holds. However, IBEX's contractor prunes out this
  // point-box because `0.2` and `0.7` are machine-representable.

  const double v1 = 0.2;
  const double v2 = 0.5;
  const double v3 = 0.7;

  // Double check the arithmetic first.
  EXPECT_EQ(v1 + v2 - v3, 0.0);

  const auto& x = ibex::ExprSymbol::new_();
  const auto& y = ibex::ExprSymbol::new_();
  const auto& z = ibex::ExprSymbol::new_();
  ibex::Function f(x, y, z, x + y - z);
  ibex::IntervalVector box(3);

  // Note that the use of BloatPoint is necessary here. Otherwise, we have an
  // empty box after pruning.
  box[0] = BloatPoint(v1);
  box[1] = BloatPoint(v2);
  box[2] = BloatPoint(v3);

  ibex::CtcFwdBwd c(f);
  c.contract(box);

  EXPECT_FALSE(box.is_empty());
}

}  // namespace
}  // namespace dreal
