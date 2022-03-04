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
#include "dreal/util/timer.h"

#include <gtest/gtest.h>

namespace dreal {
namespace {

void DoSomeWork(const int n) {
  int dummy{0};
  for (int i = 0; i < n; ++i) {
    dummy += i;
  }
  (void)dummy;
}

GTEST_TEST(Timer, Test1) {
  Timer timer;

  // Timer is not started.
  EXPECT_FALSE(timer.is_running());
  EXPECT_EQ(timer.elapsed(), Timer::clock::duration{0});

  // Start the timer.
  timer.start();
  DoSomeWork(1000);
  EXPECT_TRUE(timer.is_running());
  const auto duration1{timer.elapsed()};
  EXPECT_GT(duration1, Timer::clock::duration{0});

  // Pause the timer.
  timer.pause();
  EXPECT_FALSE(timer.is_running());
  const auto duration2{timer.elapsed()};
  DoSomeWork(1000);
  const auto duration3{timer.elapsed()};
  // Timer has been paused between duration2 and duration3.
  EXPECT_EQ(duration2, duration3);

  // Pause the timer.
  timer.resume();
  DoSomeWork(1000);
  const auto duration4{timer.elapsed()};
  EXPECT_LT(duration3, duration4);
  EXPECT_TRUE(timer.is_running());

  // Start the timer, this should reset it.
  timer.start();
  DoSomeWork(10);
  const auto duration5{timer.elapsed()};
  EXPECT_LE(duration5, duration1);
  EXPECT_TRUE(timer.is_running());
}
}  // namespace
}  // namespace dreal
