/*
   Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

#include "dreal/optimization/cached_expression.h"

#include <utility>

#include "dreal/util/assert.h"

using std::ostream;

namespace dreal {

CachedExpression::CachedExpression(Expression e, const Box& box)
    : expression_{std::move(e)}, box_{&box} {
  DREAL_ASSERT(box_);
}

const Box& CachedExpression::box() const {
  DREAL_ASSERT(box_);
  return *box_;
}

Environment& CachedExpression::mutable_environment() { return environment_; }

const Environment& CachedExpression::environment() const {
  return environment_;
}

double CachedExpression::Evaluate(const Environment& env) const {
  return expression_.Evaluate(env);
}

const Expression& CachedExpression::Differentiate(const Variable& x) {
  auto it = gradient_.find(x);
  if (it == gradient_.end()) {
    // Not found.
    return gradient_.emplace_hint(it, x, expression_.Differentiate(x))->second;
  } else {
    return it->second;
  }
}

ostream& operator<<(ostream& os, const CachedExpression& expression) {
  return os << expression.expression_;
}

}  // namespace dreal
