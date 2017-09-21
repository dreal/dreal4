#include "dreal/solver/context.h"

#include <cmath>
#include <ostream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <utility>

#include "dreal/solver/assertion_filter.h"
#include "dreal/solver/sat_solver.h"
#include "dreal/solver/theory_solver.h"
#include "dreal/util/cnfizer.h"
#include "dreal/util/logging.h"
#include "dreal/util/predicate_abstractor.h"
#include "dreal/util/scoped_vector.h"

using std::experimental::optional;
using std::isfinite;
using std::move;
using std::ostringstream;
using std::runtime_error;
using std::set;
using std::stod;
using std::string;
using std::unordered_set;
using std::vector;

namespace dreal {

// The actual implementation.
class Context::Impl {
 public:
  Impl();
  explicit Impl(Config config);
  void Assert(const Formula& f);
  std::experimental::optional<Box> CheckSat();
  void DeclareVariable(const Variable& v);
  void DeclareVariable(const Variable& v, const Expression& lb,
                       const Expression& ub);
  void Minimize(const Expression& f);
  void Pop();
  void Push();
  void SetInfo(const std::string& key, const std::string& val);
  void SetInterval(const Variable& v, double lb, double ub);
  void SetLogic(const Logic& logic);
  void SetOption(const std::string& key, const std::string& val);
  const Variable& lookup_variable(const std::string& name);
  const Config& config() const { return config_; }
  Config& mutable_config() { return config_; }

 private:
  Box& box() { return boxes_.last(); }

  Config config_;
  std::experimental::optional<Logic> logic_{};
  std::unordered_map<std::string, Variable> name_to_var_map_;
  std::unordered_map<std::string, std::string> info_;
  std::unordered_map<std::string, std::string> option_;

  ScopedVector<Box> boxes_;
  ScopedVector<Formula> stack_;
  PredicateAbstractor predicate_abstractor_;
  Cnfizer cnfizer_;
  SatSolver sat_solver_;
};

Context::Impl::Impl() : sat_solver_{&cnfizer_, &predicate_abstractor_} {
  boxes_.push_back(Box{});
}

Context::Impl::Impl(Config config)
    : config_{move(config)}, sat_solver_{&cnfizer_, &predicate_abstractor_} {
  boxes_.push_back(Box{});
}

void Context::Impl::Assert(const Formula& f) {
  if (FilterAssertion(f, &box())) {
    DREAL_LOG_DEBUG("Context::Assert: {} is not added.", f);
    DREAL_LOG_DEBUG("Box=\n{}", box());
    return;
  }

  // Predicate abstract & CNFize.
  const vector<Formula> clauses{
      cnfizer_.Convert(predicate_abstractor_.Convert(f))};
  for (const Formula& f_i : clauses) {
    DREAL_LOG_DEBUG("Context::Assert: {} is added.", f_i);
    stack_.push_back(f_i);
  }
}

optional<Box> Context::Impl::CheckSat() {
  DREAL_LOG_DEBUG("Context::CheckSat()");
  DREAL_LOG_TRACE("Context::CheckSat: Box =\n{}", box());
  if (box().empty()) {
    return {};
  }
  // If false ∈ stack_, it's UNSAT.
  for (const auto& f : stack_.get_vector()) {
    if (is_false(f)) {
      return {};
    }
  }
  // If {} = stack_ ∨ {true} = stack_, it's trivially SAT.
  if (stack_.empty() || (stack_.size() == 1 && is_true(stack_.first()))) {
    return box();
  }

  sat_solver_.AddClauses(stack_.get_vector());
  TheorySolver theory_solver{config_, box()};
  while (true) {
    if (sat_solver_.CheckSat()) {
      // SAT from SATSolver.
      DREAL_LOG_DEBUG("Context::CheckSat() - Sat Check = SAT");
      if (theory_solver.CheckSat(sat_solver_.model())) {
        // SAT from TheorySolver.
        DREAL_LOG_DEBUG("Context::CheckSat() - Theroy Check = delta-SAT");
        const Box model{theory_solver.GetModel()};
        return model;
      } else {
        // UNSAT from TheorySolver.
        DREAL_LOG_DEBUG("Context::CheckSat() - Theroy Check = UNSAT");
        const unordered_set<Formula, hash_value<Formula>> explanation{
            theory_solver.GetExplanation()};
        if (explanation.empty()) {
          return {};
        } else {
          DREAL_LOG_DEBUG(
              "Context::CheckSat() - size of explanation = {} - stack "
              "size = {}",
              explanation.size(), stack_.get_vector().size());
          sat_solver_.AddLearnedClause(explanation);
        }
      }
    } else {
      // UNSAT from SATSolver. Escape the loop.
      DREAL_LOG_DEBUG("Context::CheckSat() - Sat Check = UNSAT");
      return {};
    }
  }
}

void Context::Impl::DeclareVariable(const Variable& v) {
  DREAL_LOG_DEBUG("Context::DeclareVariable({})", v);
  name_to_var_map_.emplace(v.get_name(), v);
  box().Add(v);
}

void Context::Impl::DeclareVariable(const Variable& v, const Expression& lb,
                                    const Expression& ub) {
  DeclareVariable(v);
  SetInterval(v, lb.Evaluate(), ub.Evaluate());
}

void Context::Impl::Minimize(const Expression& f) {
  DREAL_LOG_DEBUG("Context::Minimize: {} is called.", f);

  // Given e = f(x) and the current constraints ϕᵢ which
  // involves x. it constructs a universally quantified formula ψ:
  //
  //    ψ = ∀y. (⋀ⱼ ϕᵢ(y)) → f(x) ≤ f(y).
  //

  // To construct ϕᵢ(y), we need to traverse both `box()` and
  // `stack_` because some of the asserted formulas are translated
  // and applied into `box()`.
  set<Formula> phi_set;
  ExpressionSubstitution subst;  // Maps xᵢ ↦ yᵢ to build f(y₁, ..., yₙ).
  Variables quantified_variables;  // {y₁, ... yₙ}
  const Variables x_vars{f.GetVariables()};
  for (const Variable& x_i : x_vars) {
    // We add postfix '_' to name y_i
    const Variable y_i{x_i.get_name() + "_", x_i.get_type()};
    quantified_variables.insert(y_i);
    subst.emplace(x_i, y_i);
    // If `box()[x_i]` has a finite bound, let's add that information in phi_set
    // as a constraint on y_i.
    const Box::Interval& bound_on_x_i{box()[x_i]};
    const double lb_x_i{bound_on_x_i.lb()};
    const double ub_x_i{bound_on_x_i.ub()};
    if (isfinite(lb_x_i)) {
      phi_set.insert(lb_x_i <= y_i);
    }
    if (isfinite(ub_x_i)) {
      phi_set.insert(y_i <= ub_x_i);
    }
  }
  for (const Formula& constraint : stack_) {
    if (!intersect(x_vars, constraint.GetFreeVariables()).empty()) {
      // Case : xᵢ ∈ vars(constraint)
      // We need to collect constraint[xᵢ ↦ yᵢ].
      phi_set.insert(constraint.Substitute(subst));
    }
  }
  const Formula phi{make_conjunction(phi_set)};  // ⋀ⱼ ϕ(y)
  const Formula psi{
      forall(quantified_variables, imply(phi, f <= f.Substitute(subst)))};
  return Assert(psi);
}

void Context::Impl::Pop() {
  DREAL_LOG_DEBUG("Context::Pop()");
  stack_.pop();
  boxes_.pop();
  sat_solver_.Pop();
  // TODO(soonho): Pop cnfizer/predicate_abstractor_.
}

void Context::Impl::Push() {
  DREAL_LOG_DEBUG("Context::Push()");
  sat_solver_.Push();
  boxes_.push();
  boxes_.push_back(boxes_.last());
  stack_.push();
  // TODO(soonho): Push cnfizer/predicate_abstractor_.
}

void Context::Impl::SetInfo(const string& key, const string& val) {
  DREAL_LOG_DEBUG("Context::SetInfo({} ↦ {})", key, val);
  info_[key] = val;
  if (key == ":precision") {
    config_.mutable_precision().set_from_file(stod(val));
  }
}

void Context::Impl::SetInterval(const Variable& v, const double lb,
                                const double ub) {
  DREAL_LOG_DEBUG("Context::SetInterval({} = [{}, {}])", v, lb, ub);
  box()[v] = Box::Interval{lb, ub};
}

void Context::Impl::SetLogic(const Logic& logic) {
  DREAL_LOG_DEBUG("Context::SetLogic({})", logic);
  logic_ = logic;
}

void Context::Impl::SetOption(const string& key, const string& val) {
  DREAL_LOG_DEBUG("Context::SetOption({} ↦ {})", key, val);
  option_[key] = val;
  if (key == ":polytope") {
    if (val == "true") {
      config_.mutable_use_polytope().set_from_file(true);
    } else if (val == "false") {
      config_.mutable_use_polytope().set_from_file(false);
    } else {
      throw runtime_error("Fail to interpret the option: " + key + " = " + val);
    }
  }
  if (key == ":forall-polytope") {
    if (val == "true") {
      config_.mutable_use_polytope_in_forall().set_from_file(true);
    } else if (val == "false") {
      config_.mutable_use_polytope_in_forall().set_from_file(false);
    } else {
      throw runtime_error("Fail to interpret the option: " + key + " = " + val);
    }
  }
}

const Variable& Context::Impl::lookup_variable(const string& name) {
  const auto it = name_to_var_map_.find(name);
  if (it == name_to_var_map_.cend()) {
    throw runtime_error(name + " is not found in the context.");
  }
  return it->second;
}

Context::Context() : impl_{new Impl{}} {}

Context::Context(Config config) : impl_{new Impl{move(config)}} {}

void Context::Assert(const Formula& f) { impl_->Assert(f); }

optional<Box> Context::CheckSat() { return impl_->CheckSat(); }

void Context::DeclareVariable(const Variable& v) { impl_->DeclareVariable(v); }

void Context::DeclareVariable(const Variable& v, const Expression& lb,
                              const Expression& ub) {
  impl_->DeclareVariable(v, lb, ub);
}

void Context::Exit() { DREAL_LOG_DEBUG("Context::Exit()"); }

void Context::Minimize(const Expression& f) { impl_->Minimize(f); }

void Context::Maximize(const Expression& f) { impl_->Minimize(-f); }

void Context::Pop(int n) {
  DREAL_LOG_DEBUG("Context::Pop({})", n);
  if (n <= 0) {
    ostringstream oss;
    oss << "Context::Pop(n) called with n = " << n << " which is not positive.";
    throw runtime_error(oss.str());
  }
  while (n-- > 0) {
    impl_->Pop();
  }
}

void Context::Push(int n) {
  DREAL_LOG_DEBUG("Context::Push({})", n);
  if (n <= 0) {
    ostringstream oss;
    oss << "Context::Push(n) called with n = " << n
        << " which is not positive.";
    throw runtime_error(oss.str());
  }
  while (n-- > 0) {
    impl_->Push();
  }
}

void Context::SetInfo(const string& key, const string& val) {
  impl_->SetInfo(key, val);
}

void Context::SetInterval(const Variable& v, const double lb, const double ub) {
  impl_->SetInterval(v, lb, ub);
}

void Context::SetLogic(const Logic& logic) { impl_->SetLogic(logic); }

void Context::SetOption(const string& key, const string& val) {
  impl_->SetOption(key, val);
}

const Variable& Context::lookup_variable(const string& name) {
  return impl_->lookup_variable(name);
}

const Config& Context::config() const { return impl_->config(); }
Config& Context::mutable_config() { return impl_->mutable_config(); }

string Context::version() { return DREAL_VERSION_STRING; }

}  // namespace dreal
