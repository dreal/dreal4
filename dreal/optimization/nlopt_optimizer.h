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
#pragma once

#include <memory>
#include <vector>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#include <nlopt.hpp>
#pragma GCC diagnostic pop

#include "dreal/optimization/cached_expression.h"
#include "dreal/solver/config.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/nnfizer.h"

namespace dreal {

/// Wrapper class for nlopt.
class NloptOptimizer {
 public:
  /// Constructs an NloptOptimizer instance given @p algorithm and the
  /// bound @p box.
  ///
  /// @see http://nlopt.readthedocs.io/en/latest/NLopt_Algorithms, for
  /// possible values of NLopt Algorithms.
  NloptOptimizer(nlopt::algorithm algorithm, Box bound, const Config& config);

  /// Deleted copy-constructor.
  NloptOptimizer(const NloptOptimizer&) = delete;

  /// Deleted move-constructor.
  NloptOptimizer(NloptOptimizer&&) = delete;

  /// Deleted copy-assignment operator.
  NloptOptimizer& operator=(const NloptOptimizer&) = delete;

  /// Deleted move-assignment operator.
  NloptOptimizer& operator=(NloptOptimizer&&) = delete;

  /// Destructor.
  ~NloptOptimizer() = default;

  /// Specifies the objective function.
  void SetMinObjective(const Expression& objective);

  /// Specifies a constraint.
  ///
  /// @note @p formula should be one of the following kinds:
  ///      1) A relational formula (i.e. x >= y)
  ///      2) A negation of a relational formula (i.e. ¬(x > y))
  ///      3) A conjunction of 1) or 2).
  /// @throw std::runtime_error if the above condition does not meet.
  void AddConstraint(const Formula& formula);

  /// Specifies a relational constraint.
  ///
  /// @pre @p formula is a relational constraint.
  void AddRelationalConstraint(const Formula& formula);

  /// Specifies constraints.
  void AddConstraints(const std::vector<Formula>& formulas);

  /// Runs optimization. Uses @p x as an initial value for the
  /// optimization and updates it with a solution. @p opt_f will be
  /// updated with the found optimal value.
  nlopt::result Optimize(std::vector<double>* x, double* opt_f);

  /// Runs optimization.
  ///
  /// @note Constraint and objective functions possibly include
  /// non-decision variables. If this is the case, @p env should be
  /// provided so that we can have full information to evaluate those
  /// functions.
  nlopt::result Optimize(std::vector<double>* x, double* opt_f,
                         const Environment& env);

 private:
  nlopt::opt opt_;
  const Box box_;
  const double delta_{0.0};
  CachedExpression objective_;
  std::vector<std::unique_ptr<CachedExpression>> constraints_;
  const Nnfizer nnfizer_{};
};
}  // namespace dreal
