#include "dreal/symbolic/symbolic.h"

#include <iostream>
#include <type_traits>

#include <gtest/gtest.h>

using std::cout;
using std::endl;

namespace dreal {
namespace {

class FormulaHelper : public ::testing::Test {
 protected:
  const Variable b1_{"B1", Variable::Type::BOOLEAN};
  const Variable b2_{"B2", Variable::Type::BOOLEAN};
  const Variable b3_{"B3", Variable::Type::BOOLEAN};
};

TEST_F(FormulaHelper, Imply) {}

TEST_F(FormulaHelper, Iff) {}

GTEST_TEST(Symbolic, is_nothrow_move_constructible) {
  static_assert(std::is_nothrow_move_constructible<Variable>::value,
                "Formula should be nothrow_move_constructible.");
  static_assert(std::is_nothrow_move_constructible<Expression>::value,
                "Formula should be nothrow_move_constructible.");
  static_assert(std::is_nothrow_move_constructible<Formula>::value,
                "Formula should be nothrow_move_constructible.");
}

}  // namespace
}  // namespace dreal
