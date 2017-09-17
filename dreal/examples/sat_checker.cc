#include <ostream>
#include <experimental/optional>

#include "dreal/solver/context.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {
namespace {

using std::cout;
using std::endl;
using std::experimental::optional;

// Checks the delta-satisfiability of formula `f`.
optional<Box> CheckSatisfiability(const Formula& f, const double delta) {
  Context context;
  context.mutable_config().mutable_precision() = delta;
  for (const Variable& v : f.GetFreeVariables()) {
    context.DeclareVariable(v);
  }
  context.Assert(f);
  return context.CheckSat();
}

void sat_checker_main() {
  const Variable x{"x"};
  const Formula f = (0 <= x) && (x <= 3.141592) && (sin(x) >= 0.99);
  optional<Box> result = CheckSatisfiability(f, 0.001);
  if (result) {
    cout << f << " is delta-sat:\n" << *result << endl;
  } else {
    cout << f << " is unsat." << endl;
  }
}

}  // namespace
}  // namespace dreal

int main() { dreal::sat_checker_main(); }
