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
