#include "dreal/util/option_value.h"

#include <gtest/gtest.h>

namespace dreal {

GTEST_TEST(OptionValueTest, Get) {
  OptionValue<int> option1{0};
  EXPECT_EQ(option1.get(), 0);

  OptionValue<int> option2{1};
  EXPECT_EQ(option2.get(), 1);
}

GTEST_TEST(OptionValueTest, Set1) {
  OptionValue<int> option1{0};  // Set by default.
  option1.set_from_file(1);
  EXPECT_EQ(option1.get(), 1);
  option1.set_from_command_line(2);
  EXPECT_EQ(option1.get(), 2);
}

GTEST_TEST(OptionValueTest, Set2) {
  OptionValue<int> option1{0};  // Set by default.
  option1.set_from_command_line(1);
  EXPECT_EQ(option1.get(), 1);
  option1.set_from_file(2);
  EXPECT_NE(option1.get(), 2);
  EXPECT_EQ(option1.get(), 1);
}

}  // namespace dreal
