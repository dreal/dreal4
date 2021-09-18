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
#include "dreal/api/api.h"

#include <utility>

#include "dreal/solver/config.h"
#include "dreal/solver/context.h"
#include "dreal/util/assert.h"

namespace dreal {

optional<Box> CheckSatisfiability(const Formula& f, const double delta) {
  Config config;
  config.mutable_precision() = delta;
  return CheckSatisfiability(f, config);
}

optional<Box> CheckSatisfiability(const Formula& f, Config config) {
  Context context{std::move(config)};
  for (const Variable& v : f.GetFreeVariables()) {
    context.DeclareVariable(v);
  }
  context.Assert(f);
  return context.CheckSat();
}

bool CheckSatisfiability(const Formula& f, const double delta, Box* const box) {
  Config config;
  config.mutable_precision() = delta;
  return CheckSatisfiability(f, config, box);
}

bool CheckSatisfiability(const Formula& f, Config config, Box* const box) {
  const optional<Box> result{CheckSatisfiability(f, std::move(config))};
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
  return Minimize(objective, constraint, config);
}

optional<Box> Minimize(const Expression& objective, const Formula& constraint,
                       Config config) {
  Context context{std::move(config)};
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
  return Minimize(objective, constraint, config, box);
}

bool Minimize(const Expression& objective, const Formula& constraint,
              Config config, Box* const box) {
  const optional<Box> result{
      Minimize(objective, constraint, std::move(config))};
  if (result) {
    DREAL_ASSERT(box);
    *box = *result;
    return true;
  } else {
    return false;
  }
}

}  // namespace dreal
