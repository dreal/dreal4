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
#include "dreal/util/filesystem.h"

#include <gtest/gtest.h>

namespace dreal {
namespace {

using std::string;

GTEST_TEST(FilesystemTest, GetExtension1) {
  const string f{"01.smt2"};
  EXPECT_EQ(get_extension(f), "smt2");
}

GTEST_TEST(FilesystemTest, GetExtension2) {
  const string f{"abc_def.gh.smt2"};
  EXPECT_EQ(get_extension(f), "smt2");
}

GTEST_TEST(FilesystemTest, GetExtension3) {
  const string f{"01.dr"};
  EXPECT_EQ(get_extension(f), "dr");
}

GTEST_TEST(FilesystemTest, GetExtension4) {
  const string f{"123_456.789.dr"};
  EXPECT_EQ(get_extension(f), "dr");
}

GTEST_TEST(FilesystemTest, GetExtension5) {
  const string f{"123_456_789"};
  EXPECT_EQ(get_extension(f), "");
}

}  // namespace
}  // namespace dreal
