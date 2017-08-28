#pragma once

namespace dreal {

class Config {
 public:
  Config() = default;
  ~Config() = default;

  /// Returns the precision option.
  double precision() const;

  /// Sets @p precision option.
  void set_precision(double precision);

  /// Returns the produce_models option.
  bool produce_models() const;

  /// Sets @p produce_models option.
  void set_produce_models(bool produce_models);

  /// Returns whether it uses polytope contractors or not.
  bool use_polytope() const;

  /// Sets the value of use_polytope.
  void set_use_polytope(bool value);

  /// Returns whether it uses polytope contractors inside forall contractors.
  bool use_polytope_in_forall() const;

  /// Sets the value of use_polytope_in_forall.
  void set_use_polytope_in_forall(bool value);

 private:
  double precision_{0.0};
  bool produce_models_{false};
  bool use_polytope_{false};
  bool use_polytope_in_forall_{false};
};
}  // namespace dreal
