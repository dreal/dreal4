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

#include <ostream>

#include "dreal/solver/brancher.h"
#include "dreal/util/box.h"
#include "dreal/util/dynamic_bitset.h"
#include "dreal/util/option_value.h"

namespace dreal {

class Config {
 public:
  Config() = default;
  Config(const Config&) = default;
  Config(Config&&) = default;
  Config& operator=(const Config&) = default;
  Config& operator=(Config&&) = default;
  ~Config() = default;

  using Brancher = std::function<int(
      const Box& box, const DynamicBitset& bitset, Box* left, Box* right)>;

  /// Returns the precision option.
  double precision() const;

  /// Returns a mutable OptionValue for 'precision'.
  OptionValue<double>& mutable_precision();

  /// Returns the produce_models option.
  bool produce_models() const;

  /// Returns a mutable OptionValue for 'produce_models'.
  OptionValue<bool>& mutable_produce_models();

  /// Returns whether it uses polytope contractors or not.
  bool use_polytope() const;

  /// Returns a mutable OptionValue for 'use_polytope'.
  OptionValue<bool>& mutable_use_polytope();

  /// Returns whether it uses polytope contractors inside forall contractors.
  bool use_polytope_in_forall() const;

  /// Returns a mutable OptionValue for 'use_polytope_in_forall'.
  OptionValue<bool>& mutable_use_polytope_in_forall();

  /// Returns whether it uses worklist-fixpoint algorithm.
  bool use_worklist_fixpoint() const;

  /// Returns a mutable OptionValue for 'use_worklist_fixpoint'.
  OptionValue<bool>& mutable_use_worklist_fixpoint();

  /// Returns whether it uses local optimization algorithm in exist-forall
  /// problems.
  bool use_local_optimization() const;

  /// Returns a mutable OptionValue for 'use_local_optimization'.
  OptionValue<bool>& mutable_use_local_optimization();

  /// Returns whether it uses local optimization algorithm in exist-forall
  /// problems.
  bool dump_theory_literals() const;

  /// Returns a mutable OptionValue for 'dump_theory_literals'.
  OptionValue<bool>& mutable_dump_theory_literals();

  /// Returns the number of parallel jobs.
  int number_of_jobs() const;

  /// Returns a mutable OptionValue for 'number_of_jobs'.
  OptionValue<int>& mutable_number_of_jobs();

  /// Returns whether the ICP algorithm stacks the left box first
  /// after branching.
  bool stack_left_box_first() const;

  /// Returns a mutable OptionValue for 'stack_left_box_first'.
  OptionValue<bool>& mutable_stack_left_box_first();

  /// Returns the brancher.
  const Brancher& brancher() const;

  /// Returns a mutable OptionValue for `brancher`.
  OptionValue<Brancher>& mutable_brancher();

  /// @name NLopt Options
  ///
  /// Specifies stopping criteria of NLopt. See
  /// https://nlopt.readthedocs.io/en/latest/NLopt_Reference/#stopping-criteria
  /// for more information.
  ///
  /// @{

  /// Returns relative tolerance on function value in NLopt.
  double nlopt_ftol_rel() const;

  /// Returns a mutable OptionValue for `nlopt_ftol_rel`.
  OptionValue<double>& mutable_nlopt_ftol_rel();

  /// Returns absolute tolerance on function value in NLopt.
  double nlopt_ftol_abs() const;

  /// Returns a mutable OptionValue for `nlopt_ftol_abs`.
  OptionValue<double>& mutable_nlopt_ftol_abs();

  // Returns the number of maximum function evaluations allowed in NLopt.
  int nlopt_maxeval() const;

  /// Returns a mutable OptionValue for `nlopt_maxeval`.
  OptionValue<int>& mutable_nlopt_maxeval();

  /// Returns the maxtime in NLopt.
  double nlopt_maxtime() const;

  /// Returns a mutable OptionValue for `nlopt_maxtime`.
  OptionValue<double>& mutable_nlopt_maxtime();

  enum class SatDefaultPhase {
    False = 0,
    True = 1,
    JeroslowWang = 2,  // Default option
    RandomInitialPhase = 3
  };

  /// Returns the default phase for SAT solver.
  SatDefaultPhase sat_default_phase() const;

  /// Returns a mutable OptionValue for `sat_default_phase`.
  OptionValue<SatDefaultPhase>& mutable_sat_default_phase();

  /// Returns the random seed.
  uint32_t random_seed() const;

  /// Returns a mutable OptionValue for `random_seed`.
  OptionValue<uint32_t>& mutable_random_seed();

  /// Returns if it's smtlib2_compliant mode.
  bool smtlib2_compliant() const;

  /// Returns a mutable OptionValue for `smtlib2_compliant`.
  OptionValue<bool>& mutable_smtlib2_compliant();

  /// @}

  static constexpr double kDefaultPrecision{0.001};
  static constexpr double kDefaultNloptFtolRel{1e-6};
  static constexpr double kDefaultNloptFtolAbs{1e-6};
  static constexpr int kDefaultNloptMaxEval{100};
  static constexpr double kDefaultNloptMaxTime{0.01};

 private:
  // NOTE: Make sure to match the default values specified here with the ones
  // specified in dreal/dreal_main.cc.
  OptionValue<double> precision_{kDefaultPrecision};
  OptionValue<bool> produce_models_{false};
  OptionValue<bool> use_polytope_{false};
  OptionValue<bool> use_polytope_in_forall_{false};
  OptionValue<bool> use_worklist_fixpoint_{false};
  OptionValue<bool> use_local_optimization_{false};
  OptionValue<bool> dump_theory_literals_{false};
  OptionValue<int> number_of_jobs_{1};
  OptionValue<bool> stack_left_box_first_{false};
  OptionValue<bool> smtlib2_compliant_{false};

  // --------------------------------------------------------------------------
  // NLopt options (stopping criteria)
  // --------------------------------------------------------------------------
  // These options are used when we use NLopt in refining
  // counterexamples via local-optimization. The following
  // descriptions are from
  // https://nlopt.readthedocs.io/en/latest/NLopt_Reference/#stopping-criteria
  //
  // Set relative tolerance on function value: stop when an
  // optimization step (or an estimate of the optimum) changes the
  // objective function value by less than tol multiplied by the
  // absolute value of the function value. (If there is any chance
  // that your optimum function value is close to zero, you might want
  // to set an absolute tolerance with nlopt_set_ftol_abs as well.)
  // Criterion is disabled if tol is non-positive.
  OptionValue<double> nlopt_ftol_rel_{kDefaultNloptFtolRel};

  // Set absolute tolerance on function value: stop when an
  // optimization step (or an estimate of the optimum) changes the
  // function value by less than tol. Criterion is disabled if tol is
  // non-positive.
  OptionValue<double> nlopt_ftol_abs_{kDefaultNloptFtolAbs};

  // Stop when the number of function evaluations exceeds
  // maxeval. (This is not a strict maximum: the number of function
  // evaluations may exceed maxeval slightly, depending upon the
  // algorithm.) Criterion is disabled if maxeval is non-positive.
  OptionValue<int> nlopt_maxeval_{kDefaultNloptMaxEval};

  // Stop when the optimization time (in seconds) exceeds
  // maxtime. (This is not a strict maximum: the time may exceed
  // maxtime slightly, depending upon the algorithm and on how slow
  // your function evaluation is.) Criterion is disabled if maxtime is
  // non-positive.
  OptionValue<double> nlopt_maxtime_{kDefaultNloptMaxTime};

  // Default initial phase (for PICOSAT):
  //   0 = false
  //   1 = true
  //   2 = Jeroslow-Wang (default)
  //   3 = random initial phase
  OptionValue<SatDefaultPhase> sat_default_phase_{
      SatDefaultPhase::JeroslowWang};

  // Seed for Random Number Generator.
  OptionValue<uint32_t> random_seed_{0};

  // Brancher to use. By default it uses `BranchLargestFirst`.
  OptionValue<Brancher> brancher_{BranchLargestFirst};
};
std::ostream& operator<<(std::ostream& os,
                         const Config::SatDefaultPhase& sat_default_phase);

std::ostream& operator<<(std::ostream& os, const Config& config);

}  // namespace dreal
