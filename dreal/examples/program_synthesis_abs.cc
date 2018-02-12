#include <iostream>

#include "dreal/api/api.h"
#include "dreal/symbolic/symbolic.h"

namespace dreal {
void synthesize_abs() {
  const Variable x{"x"};
  const Variable a{"a"};
  const Variable b{"b"};
  const Variable c{"c"};

  const Formula nested{
      imply(-1000 <= x && x <= 1000,
            imply(x >= c, abs(x) == a * x) && imply(x < c, abs(x) == b * x))};
  const Formula quantified{forall({x}, nested)};

  Config config;
  config.mutable_precision() = 0.001;
  config.mutable_use_polytope_in_forall() = true;
  config.mutable_use_local_optimization() = true;
  const auto result =
      CheckSatisfiability(-100 <= a && a <= 100 && -100 <= b && b <= 100 &&
                              -100 <= c && c <= 100 && quantified,
                          config);
  if (result) {
    std::cerr << *result << std::endl;
  } else {
    std::cerr << "Failed!" << std::endl;
  }
}
}  // namespace dreal

int main() { dreal::synthesize_abs(); }
