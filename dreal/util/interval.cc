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
#include "dreal/util/interval.h"

#include <cmath>
#include <limits>

namespace dreal {

using std::nextafter;
using std::numeric_limits;

Box::Interval BloatPoint(const double c) {
  const double lb{nextafter(c, -numeric_limits<double>::infinity())};
  const double ub{nextafter(c, +numeric_limits<double>::infinity())};
  return Box::Interval(lb, ub);
}
}  // namespace dreal
