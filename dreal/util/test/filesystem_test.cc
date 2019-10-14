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
