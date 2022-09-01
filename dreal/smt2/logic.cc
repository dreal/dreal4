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
  if (s == "ALL") {
    return Logic::ALL;
  }
  if (s == "QF_LIA") {
    return Logic::QF_LIA;
  }
  if (s == "QF_LIRA") {
    return Logic::QF_LIRA;
  }
  if (s == "QF_LRA") {
    return Logic::QF_LRA;
  }
  if (s == "QF_NIA") {
    return Logic::QF_NIA;
  }
  if (s == "QF_NIAT") {
    return Logic::QF_NIAT;
  }
  if (s == "QF_NIRA") {
    return Logic::QF_NIRA;
  }
  if (s == "QF_NIRAT") {
    return Logic::QF_NIRAT;
  }
  if (s == "QF_NRA") {
    return Logic::QF_NRA;
  }
  if (s == "QF_NRAT") {
    return Logic::QF_NRAT;
  }
  if (s == "QF_RDL") {
    return Logic::QF_RDL;
  }
  throw DREAL_RUNTIME_ERROR("set-logic({}) is not supported.", s);
}

ostream& operator<<(ostream& os, const Logic& logic) {
  switch (logic) {
    case Logic::ALL:
      return os << "ALL";
    case Logic::QF_LIA:
      return os << "QF_LIA";
    case Logic::QF_LIRA:
      return os << "QF_LIRA";
    case Logic::QF_LRA:
      return os << "QF_LRA";
    case Logic::QF_NIA:
      return os << "QF_NIA";
    case Logic::QF_NIAT:
      return os << "QF_NIAT";
    case Logic::QF_NIRA:
      return os << "QF_NIRA";
    case Logic::QF_NIRAT:
      return os << "QF_NIRAT";
    case Logic::QF_NRA:
      return os << "QF_NRA";
    case Logic::QF_NRAT:
      return os << "QF_NRAT";
    case Logic::QF_RDL:
      return os << "QF_RDL";
  }
  DREAL_UNREACHABLE();
}
}  // namespace dreal
