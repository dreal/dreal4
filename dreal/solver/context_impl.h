#pragma once

#include "dreal/solver/context.h"

#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "dreal/solver/sat_solver.h"
#include "dreal/solver/theory_solver.h"
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
  // Add the variable @p v to the current box. This is used to
  // introduce a non-model variable to solver. For a model variable,
  // `DeclareVariable` should be used. But `DeclareVariable` should be
  // called from outside of this class. Any methods in this class
  // should not call it directly.
  void AddToBox(const Variable& v);

  // Returns the current box in the stack.
  std::experimental::optional<Box> CheckSatCore(
      const ScopedVector<Formula>& stack, Box box, SatSolver* sat_solver);

  Box& box() { return boxes_.last(); }

  // Marks variable @p v as a model variable
  void mark_model_variable(const Variable& v);

  // Checks if the variable @p v is a model variable or not.
  bool is_model_variable(const Variable& v) const;

  // Extracts a model from the @p box. Note that @p box might include
  // non-model variables (i.e. variables introduced by if-then-else
  // elimination). This function creates a new box which is free of
  // those non-model variables.
  Box ExtractModel(const Box& box) const;

  Config config_;
  std::experimental::optional<Logic> logic_{};
  std::unordered_map<std::string, std::string> info_;
  std::unordered_map<std::string, std::string> option_;

  // Stack of boxes. The top one is the current box.
  ScopedVector<Box> boxes_;
  // Stack of asserted formulas.
  ScopedVector<Formula> stack_;
  SatSolver sat_solver_;
  std::unordered_set<Variable::Id> model_variables_;
  TheorySolver theory_solver_;
};

}  // namespace dreal
