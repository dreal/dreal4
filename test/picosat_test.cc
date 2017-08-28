#include "./picosat.h"

#include <iostream>

#include <gtest/gtest.h>

using std::cerr;
using std::endl;

int main() {
  PicoSAT* p = picosat_init();

  // Add a clause (x ∨ y). (where x = 1 and y = 2);
  picosat_add(p, 1);
  picosat_add(p, 2);
  picosat_add(p, 0);

  // Add a clause (!x ∨ !y).
  picosat_add(p, -1);
  picosat_add(p, -2);
  picosat_add(p, 0);

  // Add a clause (x);
  picosat_add(p, 1);
  picosat_add(p, 0);

  // Check satisfiability.
  int res = picosat_sat(p, -1);

  EXPECT_EQ(PICOSAT_SATISFIABLE, res);
  EXPECT_EQ(picosat_deref(p, 1), 1 /* true */);    // x ↦ true.
  EXPECT_EQ(picosat_deref(p, 2), -1 /* false */);  // y ↦ false.

  // Add a clause (y);
  picosat_add(p, 2);
  picosat_add(p, 0);

  // Check satisfiability.
  res = picosat_sat(p, -1);
  EXPECT_EQ(PICOSAT_UNSATISFIABLE, res);

  picosat_reset(p);

  return 0;
}
