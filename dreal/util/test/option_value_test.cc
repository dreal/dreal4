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
