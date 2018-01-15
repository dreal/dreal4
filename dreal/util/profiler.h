#pragma once
#include <chrono>
#include <iostream>
#include <string>

namespace dreal {
class Profiler {
 public:
  explicit Profiler(std::string name, std::ostream& out = std::cerr);
  Profiler(const Profiler&) = delete;
  Profiler(Profiler&&) = delete;
  Profiler& operator=(const Profiler&) = delete;
  Profiler& operator=(Profiler&&) = delete;
  ~Profiler();

 private:
  const std::string name_;
  std::ostream& out_;
  const std::chrono::high_resolution_clock::time_point begin_;
};
}  // namespace dreal
