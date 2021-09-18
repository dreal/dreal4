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
