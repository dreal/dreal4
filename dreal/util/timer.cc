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
