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
#include "dreal/util/logging.h"

#include <iostream>

#include <gtest/gtest.h>

namespace dreal {

GTEST_TEST(Logging, DrealLogTraceSideEffect) {
  int x = 0;

  log()->set_level(spdlog::level::off);
  // The following should cause no side-effects.
  DREAL_LOG_TRACE("x = {}", x++);
  EXPECT_EQ(x, 0);

  log()->set_level(spdlog::level::critical);
  // The following should cause no side-effects.
  DREAL_LOG_TRACE("x = {}", x++);
  EXPECT_EQ(x, 0);

  log()->set_level(spdlog::level::err);
  // The following should cause no side-effects.
  DREAL_LOG_TRACE("x = {}", x++);
  EXPECT_EQ(x, 0);

  log()->set_level(spdlog::level::warn);
  // The following should cause no side-effects.
  DREAL_LOG_TRACE("x = {}", x++);
  EXPECT_EQ(x, 0);

  log()->set_level(spdlog::level::info);
  // The following should cause no side-effects.
  DREAL_LOG_TRACE("x = {}", x++);
  EXPECT_EQ(x, 0);

  log()->set_level(spdlog::level::debug);
  // The following should cause no side-effects.
  DREAL_LOG_TRACE("x = {}", x++);
  EXPECT_EQ(x, 0);

  log()->set_level(spdlog::level::trace);
  // The following should cause side-effects.
  DREAL_LOG_TRACE("x = {}", x++);
  EXPECT_EQ(x, 1);
}

GTEST_TEST(Logging, DrealLogDebugSideEffect) {
  int x = 0;

  log()->set_level(spdlog::level::off);
  // The following should cause no side-effects.
  DREAL_LOG_DEBUG("x = {}", x++);
  EXPECT_EQ(x, 0);

  log()->set_level(spdlog::level::critical);
  // The following should cause no side-effects.
  DREAL_LOG_DEBUG("x = {}", x++);
  EXPECT_EQ(x, 0);

  log()->set_level(spdlog::level::err);
  // The following should cause no side-effects.
  DREAL_LOG_DEBUG("x = {}", x++);
  EXPECT_EQ(x, 0);

  log()->set_level(spdlog::level::warn);
  // The following should cause no side-effects.
  DREAL_LOG_DEBUG("x = {}", x++);
  EXPECT_EQ(x, 0);

  log()->set_level(spdlog::level::info);
  // The following should cause no side-effects.
  DREAL_LOG_DEBUG("x = {}", x++);
  EXPECT_EQ(x, 0);

  log()->set_level(spdlog::level::debug);
  // The following should no side-effects.
  DREAL_LOG_DEBUG("x = {}", x++);
  EXPECT_EQ(x, 1);

  log()->set_level(spdlog::level::trace);
  // The following should cause side-effects.
  DREAL_LOG_DEBUG("x = {}", x++);
  EXPECT_EQ(x, 2);
}

}  // namespace dreal
