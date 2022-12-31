/*
   Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
#include <algorithm>
#include <functional>
#include <iostream>
#include <thread>
#include <vector>

#include <cds/container/mspriority_queue.h>
#include <gtest/gtest.h>

using std::thread;
using std::vector;

// The purpose of this test is to illustrate how to use the MSPriorityQueue
// class in libcds.

namespace {

// This is a dummy class which has value_ and score_ member fields. Its
// CustomCompare is implemented to demonstrate how to use MSPriorityQueue with a
// custom comparator.
class DummyT {
 public:
  DummyT(int v, int s) : value_{v}, score_{s} {}
  int value_{};
  int score_{};
  struct CustomCompare {
    int operator()(const DummyT& b1, const DummyT& b2) {
      return b1.score_ - b2.score_;
    }
  };
};

using dyn_buffer_type = cds::opt::v::initialized_dynamic_buffer<char>;

using PriorityQueue = cds::container::MSPriorityQueue<
    DummyT, cds::container::mspriority_queue::make_traits<
                cds::opt::buffer<dyn_buffer_type>,
                /* Note that this is where we specify a custom comparator. */
                cds::opt::compare<DummyT::CustomCompare>>::type>;

constexpr int kPerQueue = 100;
constexpr int kNumThread = 8;

void push_to_pqueue(PriorityQueue* const pqueue, int thread_id) {
  for (int i = 0; i < kPerQueue; ++i) {
    pqueue->push(DummyT{i, thread_id * i + i});
  }
}

GTEST_TEST(CdsTest, PriorityQueue) {
  PriorityQueue pqueue(1024);
  EXPECT_EQ(pqueue.size(), 0);
  EXPECT_TRUE(pqueue.empty());

  vector<thread> thread_list(kNumThread);
  for (int i = 0; i < kNumThread; i++) {
    thread_list[i] = thread(push_to_pqueue, &pqueue, i);
  }

  for (auto& thread : thread_list) {
    thread.join();
  }

  EXPECT_EQ(pqueue.size(), kPerQueue * kNumThread);
  EXPECT_FALSE(pqueue.empty());

  DummyT tmp{0, 0};
  int score = 999999999;  // a dummy max score.
  while (!pqueue.empty()) {
    pqueue.pop(tmp);
    // This make sures that the returned items are sorted in descending order.
    EXPECT_TRUE(score >= tmp.score_);
    score = tmp.score_;
    std::cerr << tmp.value_ << ", " << tmp.score_ << "\n";
  }
}
}  // namespace
