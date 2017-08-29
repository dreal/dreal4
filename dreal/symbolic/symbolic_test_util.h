/// @file symbolic_test_util.h
///
/// This is the header file that we consolidate Drake's symbolic test
/// predicates originally defined in
/// "drake/common/test/symbolic_test_util.h". Other files in dreal
/// should include "dreal/symbolic/symbolic_test_util.h" and have
/// "//dreal/symbolic:symbolic_test_util" in BUILD file.
#pragma once

#include "symbolic/test/symbolic_test_util.h"

namespace dreal {

using drake::symbolic::test::FormulaEqual;
using drake::symbolic::test::VarEqual;

}  // namespace dreal
