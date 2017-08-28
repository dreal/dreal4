#include "dreal/smt2/logic.h"

#include <ostream>
#include <stdexcept>

namespace dreal {

using std::runtime_error;

Logic parse_logic(const std::string& s) {
  if (s == "QF_NRA") {
    return Logic::QF_NRA;
  }
  if (s == "QF_NRA_ODE") {
    return Logic::QF_NRA_ODE;
  }
  throw runtime_error("set-logic(" + s + ") is not supported.");
}

std::ostream& operator<<(std::ostream& os, const Logic& logic) {
  switch (logic) {
    case Logic::QF_NRA:
      return os << "QF_NRA";
    case Logic::QF_NRA_ODE:
      return os << "QF_NRA_ODE";
  }
  throw runtime_error("Should not be reachable");
}
}  // namespace dreal
