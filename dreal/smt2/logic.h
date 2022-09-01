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

#include <ostream>
#include <string>

namespace dreal {

enum class Logic {
  ALL,
  QF_LIA,
  QF_LIRA,
  QF_LRA,
  QF_NIA,
  QF_NIAT,
  QF_NIRA,
  QF_NIRAT,
  QF_NRA,
  QF_NRAT,
  QF_RDL,
};

Logic parse_logic(const std::string& s);
std::ostream& operator<<(std::ostream& os, const Logic& logic);

}  // namespace dreal
