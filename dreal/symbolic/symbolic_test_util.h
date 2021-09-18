/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
/// @file symbolic_test_util.h
///
/// This is the header file that we consolidate Drake's symbolic test
/// predicates originally defined in
/// "drake/common/test/symbolic_test_util.h". Other files in dreal
/// should include "dreal/symbolic/symbolic_test_util.h" and have
/// "//dreal/symbolic:symbolic_test_util" in BUILD file.
#pragma once

#include "dreal/symbolic/test/symbolic_test_util.h"

namespace dreal {

// NOLINTNEXTLINE(build/namespaces)
using namespace drake::symbolic::test;

}  // namespace dreal
