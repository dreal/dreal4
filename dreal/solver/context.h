#pragma once

#include <memory>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include <experimental/optional>

#include "dreal/smt2/logic.h"
#include "dreal/solver/config.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/version.h"

namespace dreal {

/// TODO(soonho): add documentation.
class Context {
 public:
  /// Constructs a context with an empty configuration.
  Context();

  /// Constructs a context with @p config.
  explicit Context(Config config);

  /// Asserts a formula @p f.
  void Assert(const Formula& f);

  /// Checks the satisfiability of the asserted formulas.
  std::experimental::optional<Box> CheckSat();

  /// Declare a variable @p v.
  void DeclareVariable(const Variable& v);

  /// Declare a variable @p v which is bounded by an interval `[lb, ub]`.
  void DeclareVariable(const Variable& v, const Expression& lb,
                       const Expression& ub);

  /// Closes the context.
  void Exit();

  /// Asserts a formula maximizing a cost function @p f.
  void Minimize(const Expression& f);

  /// Asserts a formula minimizing a cost function @p f.
  void Maximize(const Expression& f);

  /// Pops @p n stacks.
  void Pop(int n);

  /// Pushes @p n stacks.
  void Push(int n);

  /// Sets an info @p key with a value @p val.
  void SetInfo(const std::string& key, double val);

  /// Sets an info @p key with a value @p val.
  void SetInfo(const std::string& key, const std::string& val);

  /// Sets the interval of @p v in the current box (top one in boxes_).
  void SetInterval(const Variable& v, double lb, double ub);

  /// Sets the current logic to be @p logic.
  void SetLogic(const Logic& logic);

  /// Sets an option @p key with a value @p val.
  void SetOption(const std::string& key, double val);

  /// Sets an option @p key with a value @p val.
  void SetOption(const std::string& key, const std::string& val);

  /// Returns a variable associated with a name @p name.
  ///
  /// @throws if no variable is associated with @p name.
  const Variable& lookup_variable(const std::string& name);

  const Config& config() const;

  Config& mutable_config();

  static std::string version();

 private:
  // This header is exposed to external users as a part of API. We use
  // PIMPL idiom to hide internals and to reduce number of '#includes' in this
  // file.
  class Impl;

  // TODO(soonho): use copyable unique_ptr to improve performance.
  std::shared_ptr<Impl> impl_{};
};
}  // namespace dreal
