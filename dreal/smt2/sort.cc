#include "dreal/smt2/sort.h"

#include <ostream>
#include <stdexcept>

namespace dreal {

using std::runtime_error;

Sort ParseSort(const std::string& s) {
  if (s == "Real") {
    return Sort::Real;
  }
  if (s == "Int") {
    return Sort::Int;
  }
  if (s == "Bool") {
    return Sort::Bool;
  }
  throw runtime_error(s + " is not {Real, Int, Bool}.");
}

std::ostream& operator<<(std::ostream& os, const Sort& sort) {
  switch (sort) {
    case Sort::Bool:
      return os << "Bool";
    case Sort::Int:
      return os << "Int";
    case Sort::Real:
      return os << "Real";
  }
  throw runtime_error("Should not be reachable");
}
}  // namespace dreal
