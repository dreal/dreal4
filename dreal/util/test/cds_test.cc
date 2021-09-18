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
#include "dreal/util/cds.h"

#include <gtest/gtest.h>

#include "dreal/util/box.h"

namespace dreal {
namespace {

GTEST_TEST(CdsTest, PriorityQueueInt) {
  struct IntComparator {
    int operator()(const int& r1, const int& r2) {
      if (r1 < r2) {
        return -1;
      }
      if (r1 == r2) {
        return 0;
      }
      return 1;
    }
  };

  // Initialize libcds
  cds::Initialize();
  PriorityQueue<int, IntComparator> pq(1000);
  pq.push(20);
  pq.push(30);
  pq.push(10);
  int x{};
  pq.pop(x);
  EXPECT_EQ(x, 30);
  // terminate libcds
  cds::Terminate();
}

GTEST_TEST(CdsTest, PriorityQueueBox) {
  struct BoxComparator {
    int operator()(const Box& b1, const Box& b2) {
      const double diam1 = b1.MaxDiam().first;
      const double diam2 = b2.MaxDiam().first;
      if (diam1 > diam2) {
        return 1;
      }
      if (diam2 > diam1) {
        return -1;
      }
      return 0;
    }
  };

  // Real Variables.
  const Variable x{"x"};
  const Variable y{"y"};
  const Variable z{"z"};
  const Variable w{"w"};

  // Initialize libcds
  cds::Initialize();

  Box b1;
  b1.Add(x, 3, 5);
  b1.Add(y, 6, 10);

  Box b2{b1};
  b2[x] = Box::Interval(-10, 10);

  Box b3{b1};

  PriorityQueue<Box, BoxComparator> pq(1000);
  pq.push(b1);
  pq.push(b2);
  pq.push(b3);

  Box out;
  pq.pop(out);
  EXPECT_EQ(out[x].lb(), -10.0);
  EXPECT_EQ(out[x].ub(), +10.0);

  // terminate libcds
  cds::Terminate();
}

}  // namespace
}  // namespace dreal
