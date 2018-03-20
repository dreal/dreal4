#pragma once

#include <ostream>
#include <string>

namespace dreal {

enum class Logic {
  QF_NRA,
  QF_NRA_ODE,
  QF_LRA,
  QF_RDL,
};

Logic parse_logic(const std::string& s);
std::ostream& operator<<(std::ostream& os, const Logic& logic);

}  // namespace dreal
