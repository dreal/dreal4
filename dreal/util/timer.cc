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

namespace dreal {

using std::ostream;

Timer::Timer() : last_start_{Timer::clock::now()} {}

void Timer::start() {
  last_start_ = Timer::clock::now();
  elapsed_ = clock::duration{0};
  running_ = true;
}

void Timer::pause() {
  if (running_) {
    running_ = false;
    elapsed_ += (Timer::clock::now() - last_start_);
  }
}

void Timer::resume() {
  if (!running_) {
    last_start_ = Timer::clock::now();
    running_ = true;
  }
}

bool Timer::is_running() const { return running_; }

Timer::clock::duration Timer::elapsed() const {
  if (running_) {
    return elapsed_ + (Timer::clock::now() - last_start_);
  } else {
    return elapsed_;
  }
}

std::chrono::duration<double>::rep Timer::seconds() const {
  // double representation of seconds.
  using seconds_in_double = std::chrono::duration<double>;
  return std::chrono::duration_cast<seconds_in_double>(elapsed()).count();
}

ostream& operator<<(ostream& os, const Timer& timer) {
  return os << timer.seconds() << "s";
}

TimerGuard::TimerGuard(Timer* const timer, const bool enabled,
                       const bool start_timer)
    : timer_{timer}, enabled_{enabled} {
  if (enabled_) {
    if (start_timer) {
      timer_->resume();
    }
  }
}

TimerGuard::~TimerGuard() {
  if (enabled_) {
    timer_->pause();
  }
}

void TimerGuard::pause() {
  if (enabled_) {
    timer_->pause();
  }
}

void TimerGuard::resume() {
  if (enabled_) {
    timer_->resume();
  }
}

}  // namespace dreal
