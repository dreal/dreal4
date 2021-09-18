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
#include <gtest/gtest.h>

#include "minisat/core/Solver.h"

int main() {
  Minisat::Solver solver;
  const Minisat::Var v1{solver.newVar()};
  const Minisat::Var v2{solver.newVar()};

  // clause₁ = v₁ ∨ ¬v₂
  Minisat::vec<Minisat::Lit> clause1{2};
  clause1[0] = Minisat::mkLit(v1, true);
  clause1[1] = Minisat::mkLit(v2, false);

  // clause₂ = ¬v1 ∨ v2
  Minisat::vec<Minisat::Lit> clause2{2};
  clause2[0] = Minisat::mkLit(v1, false);
  clause2[1] = Minisat::mkLit(v2, true);

  solver.addClause(clause1);
  solver.addClause(clause2);

  // Check the satisfiability of (v₁ ∨ ¬v₂) ∧ (¬v₁ ∨ v₂).
  const bool result = solver.solve();
  EXPECT_TRUE(result);
}
