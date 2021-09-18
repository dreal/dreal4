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

#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "dreal/solver/context.h"
#include "dreal/solver/sat_solver.h"
#include "dreal/solver/theory_solver.h"
#include "dreal/util/optional.h"
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
  optional<Box> CheckSat();
  void DeclareVariable(const Variable& v, bool is_model_variable);
  void SetDomain(const Variable& v, const Expression& lb, const Expression& ub);
  void Minimize(const std::vector<Expression>& functions);
  void Pop();
  void Push();
  void SetInfo(const std::string& key, double val);
  void SetInfo(const std::string& key, const std::string& val);
  void SetInterval(const Variable& v, double lb, double ub);
  void SetLogic(const Logic& logic);
  void SetOption(const std::string& key, double val);
  void SetOption(const std::string& key, const std::string& val);
  optional<std::string> GetOption(const std::string& key) const;
  const Config& config() const { return config_; }
  Config& mutable_config() { return config_; }
  const ScopedVector<Formula>& assertions() const;
  Box& box() { return boxes_.last(); }
  const Box& get_model() { return model_; }

 private:
  // Add the variable @p v to the current box. This is used to
  // introduce a non-model variable to solver. For a model variable,
  // `DeclareVariable` should be used. But `DeclareVariable` should be
  // called from outside of this class. Any methods in this class
  // should not call it directly.
  void AddToBox(const Variable& v);

  // Returns the current box in the stack.
  optional<Box> CheckSatCore(const ScopedVector<Formula>& stack, Box box,
                             SatSolver* sat_solver);

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
  optional<Logic> logic_{};
  std::unordered_map<std::string, std::string> info_;
  std::unordered_map<std::string, std::string> option_;

  // Stack of boxes. The top one is the current box.
  ScopedVector<Box> boxes_;
  // Stack of asserted formulas.
  ScopedVector<Formula> stack_;
  SatSolver sat_solver_;
  std::unordered_set<Variable::Id> model_variables_;
  TheorySolver theory_solver_;

  // Stores the result of the latest checksat.
  // Note that if the checksat result was UNSAT, this box holds an empty box.
  Box model_;
};

}  // namespace dreal
