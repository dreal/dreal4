#include "dreal/solver/sat_solver.h"

#include <iostream>
#include <vector>

#include <gtest/gtest.h>

#include "dreal/symbolic/symbolic.h"

using std::cout;
using std::endl;
using std::vector;

namespace dreal {
namespace {

// GTEST_TEST(SatSolver, Test) {
//   const Variable x("x");
//   const Variable y("y");
//   const Variable z("z");
//   const Formula f1{x == 1};
//   const Formula f2{y == 2};
//   const Formula f3{z == 3};
//   vector<Formula> formulas;
//   formulas.push_back(f1);
//   formulas.push_back(!f1);
//   formulas.push_back(f1 || f2);
//   formulas.push_back(f1 && f2);
//   formulas.push_back((f1 && f2) || (f1 && !f3));
//   formulas.push_back((f1 || f2) && (f1 || !f3));

//   cout << "--------------------------" << endl;
//   for (const auto& f : formulas) {
//     cout << "F     = " << f << endl;
//     SatSolver sat_solver{f};
//     const auto result{sat_solver.CheckSat()};
//     for (const Formula& m : result.template value_or<vector<Formula>>({})) {
//       cout << "MODEL = " << m << endl;
//     }
//     cout << "--------------------------" << endl;
//   }
// }

}  // namespace
}  // namespace dreal
