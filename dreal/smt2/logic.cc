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
  throw DREAL_RUNTIME_ERROR("set-logic({}) is not supported.", s);
}

ostream& operator<<(ostream& os, const Logic& logic) {
  switch (logic) {
    case Logic::QF_NRA:
      return os << "QF_NRA";
    case Logic::QF_NRA_ODE:
      return os << "QF_NRA_ODE";
  }
  DREAL_UNREACHABLE();
}
}  // namespace dreal
