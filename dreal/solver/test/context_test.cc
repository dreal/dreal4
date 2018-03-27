#include "dreal/solver/context.h"

#include <gtest/gtest.h>

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/logging.h"

namespace dreal {
namespace {

class ContextTest : public ::testing::Test {
 protected:
  void SetUp() override { context_.DeclareVariable(x_); }

  const Variable x_{"x"};
  Context context_;
};

TEST_F(ContextTest, MultipleCheckSat) {
  context_.Assert(x_ >= 0);
  const auto result1 = context_.CheckSat();
  EXPECT_TRUE(result1);
  context_.Assert(x_ <= 5);
  const auto result2 = context_.CheckSat();
  EXPECT_TRUE(result2);
}
}  // namespace
}  // namespace dreal
