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
