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
#include "dreal/smt2/logic.h"

#include "dreal/util/exception.h"

namespace dreal {

using std::ostream;
using std::string;

Logic parse_logic(const string& s) {
  if (s == "QF_NRA") {
    return Logic::QF_NRA;
  }
  if (s == "QF_NRA_ODE") {
    return Logic::QF_NRA_ODE;
  }
  if (s == "QF_LRA") {
    return Logic::QF_LRA;
  }
  if (s == "QF_RDL") {
    return Logic::QF_RDL;
  }
  if (s == "ALL") {
    return Logic::ALL;
  }
  throw DREAL_RUNTIME_ERROR("set-logic({}) is not supported.", s);
}

ostream& operator<<(ostream& os, const Logic& logic) {
  switch (logic) {
    case Logic::ALL:
      return os << "ALL";
    case Logic::QF_NRA:
      return os << "QF_NRA";
    case Logic::QF_NRA_ODE:
      return os << "QF_NRA_ODE";
    case Logic::QF_LRA:
      return os << "QF_LRA";
    case Logic::QF_RDL:
      return os << "QF_RDL";
  }
  DREAL_UNREACHABLE();
}
}  // namespace dreal
