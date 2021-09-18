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
#include "dreal/util/scoped_unordered_map.h"

#include <gtest/gtest.h>

namespace dreal {

GTEST_TEST(ScopedUnorderedMapTest, CopyConstruct) {
  ScopedUnorderedMap<int, int> map1;
  map1.insert(1, 2);
  map1.insert(2, 3);
  map1.insert(3, 4);

  const ScopedUnorderedMap<int, int> map2(map1);
  EXPECT_EQ(map1.size(), map2.size());
  for (const auto& p : map1) {
    const int& k = p.first;
    EXPECT_EQ(map1[k], map2[k]);
  }
}

GTEST_TEST(ScopedUnorderedMapTest, MoveConstruct) {
  ScopedUnorderedMap<int, int> map1;
  map1.insert(1, 2);
  map1.insert(2, 3);
  map1.insert(3, 4);

  const ScopedUnorderedMap<int, int> map2(std::move(map1));
  EXPECT_EQ(map2.size(), 3);
  EXPECT_EQ(map2[1], 2);
  EXPECT_EQ(map2[2], 3);
  EXPECT_EQ(map2[3], 4);
}

GTEST_TEST(ScopedUnorderedMapTest, CopyOp) {
  ScopedUnorderedMap<int, int> map1;
  map1.insert(1, 2);
  map1.insert(2, 3);
  map1.insert(3, 4);

  ScopedUnorderedMap<int, int> map2;
  map2 = map1;
  EXPECT_EQ(map1.size(), map2.size());
  for (const auto& p : map1) {
    const int& k = p.first;
    EXPECT_EQ(map1[k], map2[k]);
  }
}

GTEST_TEST(ScopedUnorderedMapTest, MoveOp) {
  ScopedUnorderedMap<int, int> map1;
  map1.insert(1, 2);
  map1.insert(2, 3);
  map1.insert(3, 4);

  ScopedUnorderedMap<int, int> map2;
  map2 = std::move(map1);
  EXPECT_EQ(map2.size(), 3);
  EXPECT_EQ(map2[1], 2);
  EXPECT_EQ(map2[2], 3);
  EXPECT_EQ(map2[3], 4);
}

GTEST_TEST(ScopedUnorderedMapTest, Clear) {
  ScopedUnorderedMap<int, int> map1;
  map1.insert(1, 2);
  map1.push();
  map1.insert(2, 3);
  map1.insert(3, 4);
  EXPECT_EQ(map1.size(), 3);

  map1.clear();
  EXPECT_EQ(map1.size(), 0);

  EXPECT_THROW(map1.pop(), std::runtime_error);
}

GTEST_TEST(ScopedUnorderedMapTest, Update) {
  ScopedUnorderedMap<int, int> map;
  map.insert(1, 2);
  EXPECT_EQ(map[1], 2);
  EXPECT_EQ(map.size(), 1);

  map.insert(1, 3);  // Update
  EXPECT_EQ(map[1], 3);
  EXPECT_EQ(map.size(), 1);

  EXPECT_THROW(map[2], std::runtime_error);
}

GTEST_TEST(ScopedUnorderedMapTest, PushPop) {
  ScopedUnorderedMap<int, int> map;
  EXPECT_TRUE(map.empty());

  map.push();

  map.insert(1, 2);
  EXPECT_EQ(map[1], 2);
  EXPECT_EQ(map.size(), 1);
  EXPECT_FALSE(map.empty());

  map.push();

  map.insert(1, 3);  // Update
  map.insert(2, 4);
  EXPECT_EQ(map.size(), 2);
  EXPECT_EQ(map[1], 3);
  EXPECT_EQ(map[2], 4);
  EXPECT_FALSE(map.empty());

  map.pop();

  EXPECT_EQ(map.size(), 1);
  EXPECT_EQ(map[1], 2);        // Old value should be restored.
  EXPECT_EQ(map.count(2), 0);  // the entry for '2' is deleted.
  EXPECT_FALSE(map.empty());

  map.pop();
  EXPECT_TRUE(map.empty());
}

}  // namespace dreal
