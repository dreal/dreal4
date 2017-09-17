#include "dreal/util/option_value.h"

#include <gtest/gtest.h>

namespace dreal {

GTEST_TEST(OptionValueTest, Get) {
  OptionValue<int> option1{0};
  EXPECT_EQ(option1.get(), 0);

  const OptionValue<int> option2{1};
  EXPECT_EQ(option2.get(), 1);
}

GTEST_TEST(OptionValueTest, Set1) {
  OptionValue<int> option{0};  // Set by default.

  option.set_from_file(1);
  EXPECT_EQ(option.get(), 1);

  option.set_from_command_line(2);
  EXPECT_EQ(option.get(), 2);

  option = 3;
  EXPECT_EQ(option.get(), 3);

  option.set_from_command_line(2);
  EXPECT_NE(option.get(), 2);
  EXPECT_EQ(option.get(), 3);

  option.set_from_file(1);
  EXPECT_NE(option.get(), 1);
  EXPECT_EQ(option.get(), 3);
}

GTEST_TEST(OptionValueTest, Set2) {
  OptionValue<int> option{0};  // Set by default.

  option.set_from_command_line(1);
  EXPECT_EQ(option.get(), 1);

  option.set_from_file(2);
  EXPECT_NE(option.get(), 2);
  EXPECT_EQ(option.get(), 1);

  const int v = 3;
  option = v;
  EXPECT_EQ(option.get(), 3);
}

}  // namespace dreal
