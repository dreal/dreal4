#include "dreal/api/api.h"

#include <utility>

#include "dreal/solver/config.h"
#include "dreal/solver/context.h"
#include "dreal/util/assert.h"

namespace dreal {

using std::experimental::optional;
using std::move;

optional<Box> CheckSatisfiability(const Formula& f, const double delta) {
  Config config;
  config.mutable_precision() = delta;
  return CheckSatisfiability(f, move(config));
}

optional<Box> CheckSatisfiability(const Formula& f, Config config) {
  Context context{move(config)};
  for (const Variable& v : f.GetFreeVariables()) {
    context.DeclareVariable(v);
  }
  context.Assert(f);
  return context.CheckSat();
}

bool CheckSatisfiability(const Formula& f, const double delta, Box* const box) {
  Config config;
  config.mutable_precision() = delta;
  return CheckSatisfiability(f, move(config), box);
}

bool CheckSatisfiability(const Formula& f, Config config, Box* const box) {
  const optional<Box> result{CheckSatisfiability(f, move(config))};
  if (result) {
    DREAL_ASSERT(box);
    *box = *result;
    return true;
  } else {
    return false;
  }
}

optional<Box> Minimize(const Expression& objective, const Formula& constraint,
                       double delta) {
  Config config;
  config.mutable_precision() = delta;
  return Minimize(objective, constraint, move(config));
}

optional<Box> Minimize(const Expression& objective, const Formula& constraint,
                       Config config) {
  // We encode the following optimization problem:
  //
  //   argminₓ objective(x) such that constraint(x) holds
  //
  // into the following logic formula:
  //
  //   ϕ = ∃x. constraint(x) ∧ [∀y. constraint(y) ⇒ objective(x) ≤ objective(y)]
  //
  // and checks the δ-satisfiability of ϕ.

  // Maps an exist_variable to a forall_variable.
  ExpressionSubstitution subst;
  Variables forall_variables;
  for (const Variable& exist_variable : objective.GetVariables()) {
    const Variable forall_variable{"forall_" + exist_variable.get_name(),
                                   exist_variable.get_type()};
    forall_variables += forall_variable;
    subst.emplace(exist_variable, forall_variable);
  }
  const Formula constraint_y{constraint.Substitute(subst)};
  const Expression objective_y{objective.Substitute(subst)};
  const Formula phi{
      constraint &&
      forall(forall_variables, imply(constraint_y, objective <= objective_y))};
  return CheckSatisfiability(phi, move(config));
}

bool Minimize(const Expression& objective, const Formula& constraint,
              const double delta, Box* const box) {
  Config config;
  config.mutable_precision() = delta;
  return Minimize(objective, constraint, move(config), box);
}

bool Minimize(const Expression& objective, const Formula& constraint,
              Config config, Box* const box) {
  const optional<Box> result{Minimize(objective, constraint, move(config))};
  if (result) {
    DREAL_ASSERT(box);
    *box = *result;
    return true;
  } else {
    return false;
  }
}

}  // namespace dreal
