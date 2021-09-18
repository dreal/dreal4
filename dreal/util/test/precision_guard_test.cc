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
#include "dreal/util/precision_guard.h"

#include <sstream>
#include <string>

#include <gtest/gtest.h>

namespace dreal {
namespace {

using std::string;
using std::stringstream;

GTEST_TEST(PrecisionGuard, Test1) {
  stringstream ss;

  constexpr double pi = 3.1415926535897931;

  ss << pi;
  EXPECT_EQ(ss.str(), "3.14159");
  ss.str(string{});

  {
    PrecisionGuard guard(&ss);
    ss << pi;
    EXPECT_EQ(ss.str(), "3.1415926535897931");
    ss.str(string{});
  }

  ss << pi;
  EXPECT_EQ(ss.str(), "3.14159");
  ss.str(string{});

  {
    PrecisionGuard guard(&ss, 10);
    ss << pi;
    EXPECT_EQ(ss.str(), "3.141592654");
    ss.str(string{});
  }
}

}  // namespace
}  // namespace dreal
