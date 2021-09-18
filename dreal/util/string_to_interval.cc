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
#include "dreal/util/string_to_interval.h"

#include "dreal/util/rounding_mode_guard.h"

namespace dreal {

using std::stod;
using std::string;

Box::Interval StringToInterval(const string& s) {
  RoundingModeGuard guard(FE_UPWARD);
  const double ub{stod(s)};
  double lb{};
  if (s[0] == '-') {
    lb = -stod(s.substr(1));
  } else {
    lb = -stod("-" + s);
  }
  return Box::Interval{lb, ub};
}

}  // namespace dreal
