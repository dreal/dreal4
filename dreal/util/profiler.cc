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
#include "dreal/util/profiler.h"

#include <utility>

using std::endl;
using std::ostream;
using std::string;

namespace dreal {
Profiler::Profiler(string name, ostream& out)
    : name_{std::move(name)},
      out_(out),
      begin_(std::chrono::high_resolution_clock::now()) {}

Profiler::~Profiler() {
  using duration = std::chrono::duration<double>;
  const auto diff = std::chrono::high_resolution_clock::now() - begin_;
  out_ << name_ << ": " << std::chrono::duration_cast<duration>(diff).count()
       << endl;
}

}  // namespace dreal
