#include "dreal/util/symbolic.h"

#include <iostream>

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

}  // namespace
}  // namespace dreal
