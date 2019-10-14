#include "dreal/contractor/contractor.h"

#include <type_traits>

#include <gtest/gtest.h>

namespace dreal {
namespace {

GTEST_TEST(ContractorTest, Test) {
  // TODO(soonho): Add more tests.
}

GTEST_TEST(ContractorTest, IsNothrowMoveConstructible) {
  static_assert(std::is_nothrow_move_constructible<Contractor>::value,
                "Contractor should be nothrow_move_constructible.");
}

}  // namespace
}  // namespace dreal
