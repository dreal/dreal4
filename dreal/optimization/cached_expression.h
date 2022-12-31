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

#include <ostream>
#include <unordered_map>

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

/// CachedExpression class wraps an Expression and a box.
///
/// It is created (i) to "cache" its gradient values which will be
/// utilized by `Differentiate` method and (ii) to provide a
/// placeholder Environment to evaluate this expression and its
/// gradient values.
class CachedExpression {
 public:
  CachedExpression() = default;
  CachedExpression(Expression e, const Box& box);
  const Box& box() const;
  Environment& mutable_environment();
  const Environment& environment() const;
  double Evaluate(const Environment& env) const;
  const Expression& Differentiate(const Variable& x);

 private:
  Expression expression_;
  Environment environment_;
  const Box* box_{nullptr};
  std::unordered_map<Variable, Expression, hash_value<Variable>> gradient_;

  friend std::ostream& operator<<(std::ostream& os,
                                  const CachedExpression& expression);
};

std::ostream& operator<<(std::ostream& os, const CachedExpression& expression);

}  // namespace dreal
