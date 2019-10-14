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
