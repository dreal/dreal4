#include "dreal/solver/sat_solver.h"

#include <gtest/gtest.h>

#include "dreal/solver/config.h"
#include "dreal/symbolic/symbolic.h"

namespace dreal {
namespace {

class SatSolverTest : public ::testing::Test {
 protected:
  const Variable b1_{"b1", Variable::Type::BOOLEAN};
  const Variable b2_{"b2", Variable::Type::BOOLEAN};

  SatSolver sat_{Config()};
};

TEST_F(SatSolverTest, Sat1) {
  // b1
  sat_.AddFormula(Formula{b1_});
  EXPECT_TRUE(sat_.CheckSat());
}

TEST_F(SatSolverTest, Sat2) {
  // b2
  sat_.AddFormula(!b1_);
  EXPECT_TRUE(sat_.CheckSat());
}

TEST_F(SatSolverTest, Sat3) {
  // b1 ∧ ¬b2
  sat_.AddFormula(b1_ && !b2_);
  EXPECT_TRUE(sat_.CheckSat());
}

TEST_F(SatSolverTest, Sat4) {
  // b1 ∧ ¬b2
  sat_.AddFormula(Formula{b1_});
  sat_.AddFormula(!b2_);
  EXPECT_TRUE(sat_.CheckSat());
}

TEST_F(SatSolverTest, Sat5) {
  // (b1 ∧ b2) ∧ (b1 ∨ b2)
  sat_.AddFormula(b1_ && b2_);
  sat_.AddFormula(b1_ || b2_);
  EXPECT_TRUE(sat_.CheckSat());
}

TEST_F(SatSolverTest, UNSAT1) {
  // b1 ∧ ¬b1
  sat_.AddFormula(Formula{b1_});
  sat_.AddFormula(!b1_);
  EXPECT_FALSE(sat_.CheckSat());
}

TEST_F(SatSolverTest, UNSAT2) {
  // (b1 ∧ b2) ∧ (¬b1 ∨ ¬b2)
  sat_.AddFormula(b1_ && b2_);
  sat_.AddFormula(!b1_ || !b2_);
  EXPECT_FALSE(sat_.CheckSat());
}

}  // namespace
}  // namespace dreal
