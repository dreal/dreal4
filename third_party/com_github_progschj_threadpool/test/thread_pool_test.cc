#include "ThreadPool/ThreadPool.h"

#include <iostream>

// From https://github.com/progschj/ThreadPool/blob/master/README.md
int main() {
  // create thread pool with 2 worker threads
  ThreadPool pool(2);

  // enqueue and store future
  auto result = pool.enqueue([](int answer) { return answer; }, 42);

  // get result from future
  if (result.get() != 42) {
    throw 1;
  }
}
