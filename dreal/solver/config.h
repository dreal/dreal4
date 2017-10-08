#pragma once
#include <ostream>

#include "dreal/util/option_value.h"

namespace dreal {

class Config {
 public:
  Config() = default;
  ~Config() = default;

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

 private:
  // NOTE: Make sure to match the default values specified here with the ones
  // specified in dreal/dreal.cc.
  OptionValue<double> precision_{0.001};
  OptionValue<bool> produce_models_{false};
  OptionValue<bool> use_polytope_{false};
  OptionValue<bool> use_polytope_in_forall_{false};
};

std::ostream& operator<<(std::ostream& os, const Config& config);
}  // namespace dreal
