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

ostream& operator<<(ostream& os, const Timer& timer) {
  // double representation of seconds.
  using seconds_in_double = std::chrono::duration<double>;
  return os << std::chrono::duration_cast<seconds_in_double>(timer.elapsed())
                   .count()
            << "s";
}

}  // namespace dreal
