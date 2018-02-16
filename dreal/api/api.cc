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
  Context context{move(config)};
  for (const Variable& v : constraint.GetFreeVariables()) {
    context.DeclareVariable(v);
  }
  for (const Variable& v : objective.GetVariables()) {
    context.DeclareVariable(v);
  }
  context.Assert(constraint);
  context.Minimize(objective);
  return context.CheckSat();
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
