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
#include "dreal/util/scoped_unordered_set.h"

#include <gtest/gtest.h>

namespace dreal {
namespace {

GTEST_TEST(ScopedUnorderedSetTest, CopyConstruct) {
  ScopedUnorderedSet<int> set1;
  set1.insert(1);
  set1.insert(2);
  set1.insert(3);

  const ScopedUnorderedSet<int> set2(set1);
  EXPECT_EQ(set1.size(), set2.size());
  for (const auto& k : set1) {
    EXPECT_EQ(set2.count(k), 1);
  }
}

GTEST_TEST(ScopedUnorderedSetTest, MoveConstruct) {
  ScopedUnorderedSet<int> set1;
  set1.insert(1);
  set1.insert(2);
  set1.insert(3);

  const ScopedUnorderedSet<int> set2(std::move(set1));
  EXPECT_EQ(set2.size(), 3);
  EXPECT_EQ(set2.count(1), 1);
  EXPECT_EQ(set2.count(2), 1);
  EXPECT_EQ(set2.count(3), 1);
}

GTEST_TEST(ScopedUnorderedSetTest, CopyOp) {
  ScopedUnorderedSet<int> set1;
  set1.insert(1);
  set1.insert(2);
  set1.insert(3);

  ScopedUnorderedSet<int> set2;
  set2 = set1;
  EXPECT_EQ(set1.size(), set2.size());
  for (const auto& k : set1) {
    EXPECT_EQ(set2.count(k), 1);
  }
}

GTEST_TEST(ScopedUnorderedSetTest, MoveOp) {
  ScopedUnorderedSet<int> set1;
  set1.insert(1);
  set1.insert(2);
  set1.insert(3);

  ScopedUnorderedSet<int> set2;
  set2 = std::move(set1);
  EXPECT_EQ(set2.size(), 3);
  EXPECT_EQ(set2.count(1), 1);
  EXPECT_EQ(set2.count(2), 1);
  EXPECT_EQ(set2.count(3), 1);
}

GTEST_TEST(ScopedUnorderedSetTest, Clear) {
  ScopedUnorderedSet<int> set1;
  set1.insert(1);
  set1.push();
  set1.insert(2);
  set1.insert(3);
  EXPECT_EQ(set1.size(), 3);

  set1.clear();
  EXPECT_EQ(set1.size(), 0);

  EXPECT_THROW(set1.pop(), std::runtime_error);
}

GTEST_TEST(ScopedUnorderedSetTest, PushPop) {
  ScopedUnorderedSet<int> set;
  EXPECT_TRUE(set.empty());

  set.push();

  set.insert(1);
  EXPECT_EQ(set.count(1), 1);
  EXPECT_EQ(set.size(), 1);
  EXPECT_FALSE(set.empty());

  set.push();

  set.insert(1);  // No op
  set.insert(2);
  EXPECT_EQ(set.size(), 2);
  EXPECT_EQ(set.count(1), 1);
  EXPECT_EQ(set.count(2), 1);
  EXPECT_FALSE(set.empty());

  set.pop();
  EXPECT_EQ(set.size(), 1);
  EXPECT_EQ(set.count(1), 1);
  EXPECT_EQ(set.count(2), 0);  // the entry for '2' is deleted.
  EXPECT_FALSE(set.empty());

  set.pop();
  EXPECT_TRUE(set.empty());
}

}  // namespace
}  // namespace dreal
