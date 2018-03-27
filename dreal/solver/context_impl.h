#pragma once

#include "dreal/solver/context.h"

#include <string>
#include <unordered_map>
#include <vector>

#include "dreal/solver/sat_solver.h"
#include "dreal/util/scoped_vector.h"

namespace dreal {

// The actual implementation.
class Context::Impl {
 public:
  Impl();
  explicit Impl(Config config);
  Impl(const Impl&) = delete;
  Impl(Impl&&) = delete;
  Impl& operator=(const Impl&) = delete;
  Impl& operator=(Impl&&) = delete;
  ~Impl() = default;

  void Assert(const Formula& f);
  std::experimental::optional<Box> CheckSat();
  void DeclareVariable(const Variable& v);
  void DeclareVariable(const Variable& v, const Expression& lb,
                       const Expression& ub);
  void Minimize(const std::vector<Expression>& functions);
  void Pop();
  void Push();
  void SetInfo(const std::string& key, double val);
  void SetInfo(const std::string& key, const std::string& val);
  void SetInterval(const Variable& v, double lb, double ub);
  void SetLogic(const Logic& logic);
  void SetOption(const std::string& key, double val);
  void SetOption(const std::string& key, const std::string& val);
  const Config& config() const { return config_; }
  Config& mutable_config() { return config_; }

 private:
  Box& box() { return boxes_.last(); }

  Config config_;
  std::experimental::optional<Logic> logic_{};
  std::unordered_map<std::string, std::string> info_;
  std::unordered_map<std::string, std::string> option_;

  ScopedVector<Box> boxes_;  // Stack of boxes. The top one is the current box.
  ScopedVector<Formula> stack_;  // Stack of asserted formulas.
  SatSolver sat_solver_;
};

}  // namespace dreal
