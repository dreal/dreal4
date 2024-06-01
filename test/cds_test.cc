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
#include <algorithm>
#include <functional>
#include <thread>
#include <vector>

#include <cds/container/treiber_stack.h>
#include <cds/gc/hp.h>  // for cds::HP (Hazard Pointer) SMR
#include <cds/init.h>   // for cds::Initialize and cds::Terminate
#include <gtest/gtest.h>

using std::for_each;
using std::mem_fn;
using std::thread;
using std::vector;

namespace {
struct StackTraits : public cds::container::treiber_stack::traits {
  typedef cds::intrusive::treiber_stack::stat<> stat;
  typedef cds::atomicity::item_counter item_counter;
};

using IntStack = cds::container::TreiberStack<cds::gc::HP, int, StackTraits>;

constexpr int kPerStack = 1000;
constexpr int kNumThread = 4;

void push_to_stack(IntStack* const stack) {
  // Attach the thread to libcds infrastructure
  cds::threading::Manager::attachThread();
  for (int i = 0; i < kPerStack; ++i) {
    stack->push(i);
  }
  // Detach thread when terminating
  cds::threading::Manager::detachThread();
}
}  // namespace

GTEST_TEST(CDS_TEST, STACK) {
  // Initialize libcds
  cds::Initialize();
  {
    // Initialize Hazard Pointer singleton
    cds::gc::HP hpGC;

    // If main thread uses lock-free containers
    // the main thread should be attached to libcds infrastructure
    cds::threading::Manager::attachThread();

    IntStack stack;
    EXPECT_EQ(stack.size(), 0);
    EXPECT_TRUE(stack.empty());

    {
      vector<thread> threadList;
      for (int i = 0; i < kNumThread; i++) {
        threadList.push_back(thread(push_to_stack, &stack));
      }
      for_each(threadList.begin(), threadList.end(), mem_fn(&thread::join));
    }
    EXPECT_EQ(stack.size(), kPerStack * kNumThread);
    EXPECT_FALSE(stack.empty());
  }
  // terminate libcds
  cds::Terminate();
}
