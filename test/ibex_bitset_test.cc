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
#include <iostream>

#include <gtest/gtest.h>

#include "./ibex.h"

namespace {

GTEST_TEST(IbexBitsetTest, Add) {
  int _bitset1[3] = {3, 7, 161};
  ibex::BitSet bitset1(3, _bitset1);
  EXPECT_TRUE(bitset1[3]);
  EXPECT_TRUE(bitset1[7]);
  EXPECT_TRUE(bitset1[161]);
  EXPECT_EQ(bitset1.size(), 3);
  EXPECT_EQ(bitset1.min(), 3);
  EXPECT_EQ(bitset1.max(), 161);

  int _bitset2[2] = {4, 7};
  ibex::BitSet bitset2(2, _bitset2);
  EXPECT_TRUE(bitset2[4]);
  EXPECT_TRUE(bitset2[7]);
  EXPECT_EQ(bitset2.size(), 2);
  EXPECT_EQ(bitset2.min(), 4);
  EXPECT_EQ(bitset2.max(), 7);

  int _bitset3[4] = {3, 4, 7, 160};
  ibex::BitSet bitset3(4, _bitset3);
  EXPECT_TRUE(bitset3[3]);
  EXPECT_TRUE(bitset3[4]);
  EXPECT_TRUE(bitset3[7]);
  EXPECT_TRUE(bitset3[160]);
  EXPECT_EQ(bitset3.size(), 4);
  EXPECT_EQ(bitset3.min(), 3);
  EXPECT_EQ(bitset3.max(), 160);

  ibex::BitSet bs(bitset1);
  bs |= bitset2;
  bs |= bitset3;
  EXPECT_TRUE(bs[3]);
  EXPECT_TRUE(bs[4]);
  EXPECT_TRUE(bs[7]);
  EXPECT_TRUE(bs[160]);
  EXPECT_TRUE(bs[161]);
  EXPECT_EQ(bs.size(), 5);
  EXPECT_EQ(bs.min(), 3);
  EXPECT_EQ(bs.max(), 161);
}

}  // namespace
