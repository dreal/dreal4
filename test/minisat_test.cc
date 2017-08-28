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
