#include "dreal/solver/context.h"

#include <algorithm>
#include <cmath>
#include <limits>
#include <ostream>
#include <set>
#include <sstream>
#include <unordered_set>

#include "dreal/solver/filter_assertion.h"
#include "dreal/solver/sat_solver.h"
#include "dreal/solver/theory_solver.h"
#include "dreal/util/assert.h"
#include "dreal/util/exception.h"
#include "dreal/util/if_then_else_eliminator.h"
#include "dreal/util/logging.h"
#include "dreal/util/scoped_vector.h"

using std::experimental::optional;
using std::find_if;
using std::isfinite;
using std::make_shared;
using std::numeric_limits;
using std::ostringstream;
using std::pair;
using std::set;
using std::string;
using std::unordered_set;
using std::vector;

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
  std::experimental::optional<Box> CheckSatCore();
  std::experimental::optional<Box> CheckSat();
  void DeclareVariable(const Variable& v);
  void DeclareVariable(const Variable& v, const Expression& lb,
                       const Expression& ub);
  void Minimize(const vector<Expression>& functions);
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

Context::Impl::Impl() { boxes_.push_back(Box{}); }

Context::Impl::Impl(Config config) : config_{config} {
  boxes_.push_back(Box{});
}

void Context::Impl::Assert(const Formula& f) {
  if (is_true(f)) {
    return;
  }
  if (box().empty()) {
    return;
  }
  if (FilterAssertion(f, &box()) == FilterAssertionResult::NotFiltered) {
    DREAL_LOG_DEBUG("Context::Assert: {} is added.", f);
    IfThenElseEliminator ite_eliminator;
    const Formula no_ite{ite_eliminator.Process(f)};
    for (const Variable& ite_var : ite_eliminator.variables()) {
      DeclareVariable(ite_var);
    }
    stack_.push_back(no_ite);
    return;
  } else {
    DREAL_LOG_DEBUG("Context::Assert: {} is not added.", f);
    DREAL_LOG_DEBUG("Box=\n{}", box());
    return;
  }
}

namespace {
// It is possible that a solution box has a dimension whose diameter
// is larger than delta when the given constraints are not tight.
// This function tighten the box @p box so that every dimension has a
// width smaller than delta.
void Tighten(Box* box, const double delta) {
  for (int i = 0; i < box->size(); ++i) {
    auto& interval = (*box)[i];
    if (interval.diam() > delta) {
      const Variable& var{box->variable(i)};
      switch (var.get_type()) {
        case Variable::Type::BINARY:
          // Always pick 1.0
          interval = 1.0;
          break;
        case Variable::Type::BOOLEAN:
          // Always pick True (1.0)
          interval = 1.0;
          break;
        case Variable::Type::CONTINUOUS: {
          const double mid{interval.mid()};
          const double half_delta{delta / 2.0};
          interval &= Box::Interval(mid - half_delta, mid + half_delta);
        } break;
        case Variable::Type::INTEGER: {
          const double mid{interval.mid()};
          interval = static_cast<int>(mid);
        } break;
      }
    }
  }
}

// The parameter @p box might include non-model variables
// (i.e. variables introduced by if-then-else elimination). This
// function creates a new box which is free of those non-model
// variables. The return value will be passed to users.
Box ExtractModel(const Box& box) {
  Box new_box;
  for (const Variable& v : box.variables()) {
    if (v.is_model_variable()) {
      new_box.Add(v, box[v].lb(), box[v].ub());
    }
  }
  return new_box;
}
}  // namespace

optional<Box> Context::Impl::CheckSatCore() {
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
  // If stack_ = ∅ or stack_ = {true}, it's trivially SAT.
  if (stack_.empty() || (stack_.size() == 1 && is_true(stack_.first()))) {
    Tighten(&box(), config_.precision());
    DREAL_LOG_DEBUG("Context::CheckSat() - Found Model\n{}", box());
    return box();
  }
  sat_solver_.AddFormulas(stack_.get_vector());

  TheorySolver theory_solver{config_, box()};
  while (true) {
    const auto optional_model = sat_solver_.CheckSat();
    if (optional_model) {
      const vector<pair<Variable, bool>>& boolean_model{optional_model->first};
      for (const pair<Variable, bool>& p : boolean_model) {
        box()[p.first] = p.second ? 1.0 : 0.0;  // true -> 1.0 and false -> 0.0
      }
      const vector<pair<Variable, bool>>& theory_model{optional_model->second};
      if (!theory_model.empty()) {
        // SAT from SATSolver.
        DREAL_LOG_DEBUG("Context::CheckSat() - Sat Check = SAT");

        vector<Formula> assertions;
        assertions.reserve(theory_model.size());
        for (const pair<Variable, bool>& p : theory_model) {
          assertions.push_back(p.second ? sat_solver_.theory_literal(p.first)
                                        : !sat_solver_.theory_literal(p.first));
        }
        if (theory_solver.CheckSat(box(), assertions)) {
          // SAT from TheorySolver.
          DREAL_LOG_DEBUG("Context::CheckSat() - Theroy Check = delta-SAT");
          Box model{theory_solver.GetModel()};
          return model;
        } else {
          // UNSAT from TheorySolver.
          DREAL_LOG_DEBUG("Context::CheckSat() - Theroy Check = UNSAT");
          const unordered_set<Formula, hash_value<Formula>>& explanation{
              theory_solver.GetExplanation()};
          DREAL_ASSERT(!explanation.empty());
          DREAL_LOG_DEBUG(
              "Context::CheckSat() - size of explanation = {} - stack "
              "size = {}",
              explanation.size(), stack_.get_vector().size());
          sat_solver_.AddLearnedClause(explanation);
        }
      } else {
        return box();
      }
    } else {
      // UNSAT from SATSolver. Escape the loop.
      DREAL_LOG_DEBUG("Context::CheckSat() - Sat Check = UNSAT");
      return {};
    }
  }
}

optional<Box> Context::Impl::CheckSat() {
  auto result = CheckSatCore();
  if (result) {
    // In case of delta-sat, do post-processing.
    Tighten(&(*result), config_.precision());
    DREAL_LOG_DEBUG("Context::CheckSat() - Found Model\n{}", *result);
    return ExtractModel(*result);
  } else {
    return result;
  }
}

void Context::Impl::DeclareVariable(const Variable& v) {
  DREAL_LOG_DEBUG("Context::DeclareVariable({})", v);
  const auto& variables = box().variables();
  if (find_if(variables.begin(), variables.end(), [&v](const Variable& v_) {
        return v.equal_to(v_);
      }) == variables.end()) {
    // v is not in box.
    box().Add(v);
  }
}

void Context::Impl::DeclareVariable(const Variable& v, const Expression& lb,
                                    const Expression& ub) {
  DeclareVariable(v);
  SetInterval(v, lb.Evaluate(), ub.Evaluate());
}

void Context::Impl::Minimize(const vector<Expression>& functions) {
  // Given objective functions f₁(x), ... fₙ(x) and the current
  // constraints ϕᵢ which involves x. it constructs a universally
  // quantified formula ψ:
  //
  //    ψ = ∀y. (⋀ᵢ ϕᵢ(y)) → (f₁(x) ≤ f₁(y) ∨ ... ∨ fₙ(x) ≤ fₙ(y))
  //      = ∀y. ¬(⋀ᵢ ϕᵢ(y)) ∨ (f₁(x) ≤ f₁(y) ∨ ... ∨ fₙ(x) ≤ fₙ(y))
  //      = ∀y. (∨ᵢ ¬ϕᵢ(y)) ∨ (f₁(x) ≤ f₁(y) ∨ ... ∨ fₙ(x) ≤ fₙ(y)).
  //
  // Note that when we have more than one objective function, this
  // encoding scheme denotes Pareto optimality.
  //
  // To construct ϕᵢ(y), we need to traverse both `box()` and
  // `stack_` because some of the asserted formulas are translated
  // and applied into `box()`.
  set<Formula> set_of_negated_phi;  // Collects ¬ϕᵢ(y).
  ExpressionSubstitution subst;  // Maps xᵢ ↦ yᵢ to build f(y₁, ..., yₙ).
  Variables quantified_variables;  // {y₁, ... yₙ}
  Variables x_vars;
  for (const Expression& f : functions) {
    x_vars += f.GetVariables();
  }
  for (const Variable& x_i : x_vars) {
    // We add postfix '_' to name y_i
    const Variable y_i{x_i.get_name() + "_", x_i.get_type()};
    quantified_variables.insert(y_i);
    subst.emplace(x_i, y_i);
    // If `box()[x_i]` has a finite bound, let's add that information in
    // set_of_negated_phi as a constraint on y_i.
    const Box::Interval& bound_on_x_i{box()[x_i]};
    const double lb_x_i{bound_on_x_i.lb()};
    const double ub_x_i{bound_on_x_i.ub()};
    if (isfinite(lb_x_i)) {
      set_of_negated_phi.insert(!(lb_x_i <= y_i));
    }
    if (isfinite(ub_x_i)) {
      set_of_negated_phi.insert(!(y_i <= ub_x_i));
    }
  }
  for (const Formula& constraint : stack_) {
    if (HaveIntersection(x_vars, constraint.GetFreeVariables())) {
      // Case : xᵢ ∈ vars(constraint)
      // We need to collect constraint[xᵢ ↦ yᵢ].
      set_of_negated_phi.insert(!constraint.Substitute(subst));
    }
  }
  Formula quantified{make_disjunction(set_of_negated_phi)};  // ∨ᵢ ¬ϕᵢ(y)
  for (const Expression& f : functions) {
    quantified = quantified || (f <= f.Substitute(subst));
  }
  const Formula psi{forall(quantified_variables, quantified)};
  return Assert(psi);
}

void Context::Impl::Pop() {
  DREAL_LOG_DEBUG("Context::Pop()");
  stack_.pop();
  boxes_.pop();
  sat_solver_.Pop();
}

void Context::Impl::Push() {
  DREAL_LOG_DEBUG("Context::Push()");
  sat_solver_.Push();
  boxes_.push();
  boxes_.push_back(boxes_.last());
  stack_.push();
}

namespace {
string to_string(const double) {
  ostringstream oss;
  oss.precision(numeric_limits<double>::max_digits10 + 2);
  return oss.str();
}
}  // namespace

void Context::Impl::SetInfo(const string& key, const double val) {
  DREAL_LOG_DEBUG("Context::SetInfo({} ↦ {})", key, val);
  info_[key] = to_string(val);
  if (key == ":precision") {
    DREAL_ASSERT(val > 0.0);
    config_.mutable_precision().set_from_file(val);
  }
}

void Context::Impl::SetInfo(const string& key, const string& val) {
  DREAL_LOG_DEBUG("Context::SetInfo({} ↦ {})", key, val);
  info_[key] = val;
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

void Context::Impl::SetOption(const string& key, const double val) {
  DREAL_LOG_DEBUG("Context::SetOption({} ↦ {})", key, val);
  option_[key] = to_string(val);
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
      throw DREAL_RUNTIME_ERROR("Fail to interpret the option: {} = {}", key,
                                val);
    }
  }
  if (key == ":forall-polytope") {
    if (val == "true") {
      config_.mutable_use_polytope_in_forall().set_from_file(true);
    } else if (val == "false") {
      config_.mutable_use_polytope_in_forall().set_from_file(false);
    } else {
      throw DREAL_RUNTIME_ERROR("Fail to interpret the option: {} = {}", key,
                                val);
    }
  }
}

Context::Context() : Context{Config{}} {}

Context::Context(Config config) : impl_{make_shared<Impl>(config)} {}

void Context::Assert(const Formula& f) { impl_->Assert(f); }

optional<Box> Context::CheckSat() { return impl_->CheckSat(); }

void Context::DeclareVariable(const Variable& v) { impl_->DeclareVariable(v); }

void Context::DeclareVariable(const Variable& v, const Expression& lb,
                              const Expression& ub) {
  impl_->DeclareVariable(v, lb, ub);
}

void Context::Exit() { DREAL_LOG_DEBUG("Context::Exit()"); }

void Context::Minimize(const Expression& f) { impl_->Minimize({f}); }

void Context::Minimize(const vector<Expression>& functions) {
  impl_->Minimize(functions);
}

void Context::Maximize(const Expression& f) { impl_->Minimize({-f}); }

void Context::Pop(int n) {
  DREAL_LOG_DEBUG("Context::Pop({})", n);
  if (n <= 0) {
    throw DREAL_RUNTIME_ERROR(
        "Context::Pop(n) called with n = {} which is not positive.", n);
  }
  while (n-- > 0) {
    impl_->Pop();
  }
}

void Context::Push(int n) {
  DREAL_LOG_DEBUG("Context::Push({})", n);
  if (n <= 0) {
    throw DREAL_RUNTIME_ERROR(
        "Context::Push(n) called with n = {} which is not positive.", n);
  }
  while (n-- > 0) {
    impl_->Push();
  }
}

void Context::SetInfo(const string& key, const double val) {
  impl_->SetInfo(key, val);
}

void Context::SetInfo(const string& key, const string& val) {
  impl_->SetInfo(key, val);
}

void Context::SetInterval(const Variable& v, const double lb, const double ub) {
  impl_->SetInterval(v, lb, ub);
}

void Context::SetLogic(const Logic& logic) { impl_->SetLogic(logic); }

void Context::SetOption(const string& key, const double val) {
  impl_->SetOption(key, val);
}

void Context::SetOption(const string& key, const string& val) {
  impl_->SetOption(key, val);
}

const Config& Context::config() const { return impl_->config(); }
Config& Context::mutable_config() { return impl_->mutable_config(); }

string Context::version() { return DREAL_VERSION_STRING; }

}  // namespace dreal
