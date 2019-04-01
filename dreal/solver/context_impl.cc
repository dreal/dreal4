#include "dreal/solver/context_impl.h"

#include <algorithm>
#include <cmath>
#include <limits>
#include <ostream>
#include <set>
#include <sstream>
#include <unordered_set>
#include <utility>

#include "dreal/solver/filter_assertion.h"
#include "dreal/util/assert.h"
#include "dreal/util/exception.h"
#include "dreal/util/if_then_else_eliminator.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::find_if;
using std::isfinite;
using std::numeric_limits;
using std::ostringstream;
using std::pair;
using std::set;
using std::string;
using std::unordered_set;
using std::vector;

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

string to_string(const double) {
  ostringstream oss;
  oss.precision(numeric_limits<double>::max_digits10 + 2);
  return oss.str();
}

bool ParseBooleanOption(const string& key, const string& val) {
  if (val == "true") {
    return true;
  }
  if (val == "false") {
    return false;
  }
  throw DREAL_RUNTIME_ERROR("Unknown value {} is provided for option {}", val,
                            key);
}
}  // namespace

Context::Impl::Impl() : Impl{Config{}} {}

Context::Impl::Impl(Config config)
    : config_{config}, sat_solver_{config_}, theory_solver_{config_} {
  boxes_.push_back(Box{});
}

void Context::Impl::Assert(const Formula& f) {
  if (is_true(f)) {
    return;
  }
  if (box().empty()) {
    return;
  }
  if (is_false(f)) {
    box().set_empty();
    return;
  }
  if (FilterAssertion(f, &box()) == FilterAssertionResult::NotFiltered) {
    DREAL_LOG_DEBUG("ContextImpl::Assert: {} is added.", f);
    IfThenElseEliminator ite_eliminator;
    const Formula no_ite{ite_eliminator.Process(f)};
    for (const Variable& ite_var : ite_eliminator.variables()) {
      // Note that the following does not mark `ite_var` as a model variable.
      AddToBox(ite_var);
    }
    stack_.push_back(no_ite);
    sat_solver_.AddFormula(no_ite);
    return;
  } else {
    DREAL_LOG_DEBUG("ContextImpl::Assert: {} is not added.", f);
    DREAL_LOG_DEBUG("Box=\n{}", box());
    return;
  }
}

optional<Box> Context::Impl::CheckSatCore(const ScopedVector<Formula>& stack,
                                          Box box,
                                          SatSolver* const sat_solver) {
  DREAL_LOG_DEBUG("ContextImpl::CheckSatCore()");
  DREAL_LOG_TRACE("ContextImpl::CheckSat: Box =\n{}", box);
  if (box.empty()) {
    return {};
  }
  // If false ∈ stack, it's UNSAT.
  for (const auto& f : stack.get_vector()) {
    if (is_false(f)) {
      return {};
    }
  }
  // If stack = ∅ or stack = {true}, it's trivially SAT.
  if (stack.empty() || (stack.size() == 1 && is_true(stack.first()))) {
    DREAL_LOG_DEBUG("ContextImpl::CheckSatCore() - Found Model\n{}", box);
    return box;
  }
  while (true) {
    const auto optional_model = sat_solver->CheckSat();
    if (optional_model) {
      const vector<pair<Variable, bool>>& boolean_model{optional_model->first};
      for (const pair<Variable, bool>& p : boolean_model) {
        box[p.first] = p.second ? 1.0 : 0.0;  // true -> 1.0 and false -> 0.0
      }
      const vector<pair<Variable, bool>>& theory_model{optional_model->second};
      if (!theory_model.empty()) {
        // SAT from SATSolver.
        DREAL_LOG_DEBUG("ContextImpl::CheckSatCore() - Sat Check = SAT");

        vector<Formula> assertions;
        assertions.reserve(theory_model.size());
        for (const pair<Variable, bool>& p : theory_model) {
          assertions.push_back(p.second ? sat_solver->theory_literal(p.first)
                                        : !sat_solver->theory_literal(p.first));
        }
        if (theory_solver_.CheckSat(box, assertions)) {
          // SAT from TheorySolver.
          DREAL_LOG_DEBUG(
              "ContextImpl::CheckSatCore() - Theroy Check = delta-SAT");
          Box model{theory_solver_.GetModel()};
          return model;
        } else {
          // UNSAT from TheorySolver.
          DREAL_LOG_DEBUG("ContextImpl::CheckSatCore() - Theroy Check = UNSAT");
          const set<Formula>& explanation{theory_solver_.GetExplanation()};
          DREAL_LOG_DEBUG(
              "ContextImpl::CheckSatCore() - size of explanation = {} - stack "
              "size = {}",
              explanation.size(), stack.get_vector().size());
          sat_solver->AddLearnedClause(explanation);
        }
      } else {
        return box;
      }
    } else {
      // UNSAT from SATSolver. Escape the loop.
      DREAL_LOG_DEBUG("ContextImpl::CheckSatCore() - Sat Check = UNSAT");
      return {};
    }
  }
}

optional<Box> Context::Impl::CheckSat() {
  auto result = CheckSatCore(stack_, box(), &sat_solver_);
  if (result) {
    // In case of delta-sat, do post-processing.
    Tighten(&(*result), config_.precision());
    DREAL_LOG_DEBUG("ContextImpl::CheckSat() - Found Model\n{}", *result);
    model_ = ExtractModel(*result);
    return model_;
  } else {
    model_.set_empty();
    return result;
  }
}

void Context::Impl::AddToBox(const Variable& v) {
  DREAL_LOG_DEBUG("ContextImpl::AddToBox({})", v);
  const auto& variables = box().variables();
  if (find_if(variables.begin(), variables.end(), [&v](const Variable& v_) {
        return v.equal_to(v_);
      }) == variables.end()) {
    // v is not in box.
    box().Add(v);
  }
}

void Context::Impl::DeclareVariable(const Variable& v,
                                    const bool is_model_variable) {
  DREAL_LOG_DEBUG("ContextImpl::DeclareVariable({})", v);
  AddToBox(v);
  if (is_model_variable) {
    mark_model_variable(v);
  }
}

void Context::Impl::SetDomain(const Variable& v, const Expression& lb,
                              const Expression& ub) {
  const double lb_fp =
      is_real_constant(lb) ? get_lb_of_real_constant(lb) : lb.Evaluate();
  const double ub_fp =
      is_real_constant(ub) ? get_ub_of_real_constant(ub) : ub.Evaluate();
  SetInterval(v, lb_fp, ub_fp);
}

void Context::Impl::Minimize(const vector<Expression>& functions) {
  // Given objective functions f₁(x), ... fₙ(x) and the current
  // constraints ϕᵢ which involves x. this method encodes them into a
  // universally quantified formula ψ:
  //
  //    ψ = ∀y. (⋀ᵢ ϕᵢ(y)) → (f₁(x) ≤ f₁(y) ∨ ... ∨ fₙ(x) ≤ fₙ(y))
  //      = ∀y. ¬(⋀ᵢ ϕᵢ(y)) ∨ (f₁(x) ≤ f₁(y) ∨ ... ∨ fₙ(x) ≤ fₙ(y))
  //      = ∀y. (∨ᵢ ¬ϕᵢ(y)) ∨ (f₁(x) ≤ f₁(y) ∨ ... ∨ fₙ(x) ≤ fₙ(y)).
  //
  // Here we introduce existential variables zᵢ for fᵢ(x) to have
  //
  //    ψ =  ∃z₁...zₙ. (z₁ = f₁(x) ∧ ... ∧ zₙ = fₙ(x)) ∧
  //              [∀y. (∨ᵢ ¬ϕᵢ(y)) ∨ (z₁ ≤ f₁(y) ∨ ... ∨ zₙ ≤ fₙ(y))].
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

  // Collects side-constraints related to the cost functions.
  unordered_set<Formula> constraints;
  bool keep_going = true;
  while (keep_going) {
    keep_going = false;
    for (const Formula& constraint : stack_) {
      if (constraints.find(constraint) == constraints.end() &&
          HaveIntersection(x_vars, constraint.GetFreeVariables())) {
        x_vars += constraint.GetFreeVariables();
        constraints.insert(constraint);
        keep_going = true;
      }
    }
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

  for (const Formula& constraint : constraints) {
    set_of_negated_phi.insert(!constraint.Substitute(subst));
  }

  Formula quantified{make_disjunction(set_of_negated_phi)};  // ∨ᵢ ¬ϕᵢ(y)
  Formula new_z_block;  // This will have (z₁ = f₁(x) ∧ ... ∧ zₙ = fₙ(x)).
  static int counter{0};
  for (const Expression& f_i : functions) {
    const Variable z_i{"Z" + std::to_string(counter++),
                       Variable::Type::CONTINUOUS};
    AddToBox(z_i);
    new_z_block = new_z_block && (z_i == f_i);
    quantified = quantified || (z_i <= f_i.Substitute(subst));
  }
  const Formula psi{new_z_block && forall(quantified_variables, quantified)};
  return Assert(psi);
}

void Context::Impl::Pop() {
  DREAL_LOG_DEBUG("ContextImpl::Pop()");
  stack_.pop();
  boxes_.pop();
  sat_solver_.Pop();
}

void Context::Impl::Push() {
  DREAL_LOG_DEBUG("ContextImpl::Push()");
  sat_solver_.Push();
  boxes_.push();
  boxes_.push_back(boxes_.last());
  stack_.push();
}

void Context::Impl::SetInfo(const string& key, const double val) {
  DREAL_LOG_DEBUG("ContextImpl::SetInfo({} ↦ {})", key, val);
  info_[key] = to_string(val);
}

void Context::Impl::SetInfo(const string& key, const string& val) {
  DREAL_LOG_DEBUG("ContextImpl::SetInfo({} ↦ {})", key, val);
  info_[key] = val;
}

void Context::Impl::SetInterval(const Variable& v, const double lb,
                                const double ub) {
  DREAL_LOG_DEBUG("ContextImpl::SetInterval({} = [{}, {}])", v, lb, ub);
  box()[v] = Box::Interval{lb, ub};
}

void Context::Impl::SetLogic(const Logic& logic) {
  DREAL_LOG_DEBUG("ContextImpl::SetLogic({})", logic);
  logic_ = logic;
}

void Context::Impl::SetOption(const string& key, const double val) {
  DREAL_LOG_DEBUG("ContextImpl::SetOption({} ↦ {})", key, val);
  option_[key] = to_string(val);
  if (key == ":precision") {
    if (val <= 0.0) {
      throw DREAL_RUNTIME_ERROR("Precision has to be positive (input = {}).",
                                val);
    }
    return config_.mutable_precision().set_from_file(val);
  }
}

void Context::Impl::SetOption(const string& key, const string& val) {
  DREAL_LOG_DEBUG("ContextImpl::SetOption({} ↦ {})", key, val);
  option_[key] = val;
  if (key == ":polytope") {
    return config_.mutable_use_polytope().set_from_file(
        ParseBooleanOption(key, val));
  }
  if (key == ":forall-polytope") {
    return config_.mutable_use_polytope_in_forall().set_from_file(
        ParseBooleanOption(key, val));
  }
  if (key == ":local-optimization") {
    return config_.mutable_use_local_optimization().set_from_file(
        ParseBooleanOption(key, val));
  }
  if (key == ":worklist-fixpoint") {
    return config_.mutable_use_worklist_fixpoint().set_from_file(
        ParseBooleanOption(key, val));
  }
  if (key == ":produce-models") {
    return config_.mutable_produce_models().set_from_file(
        ParseBooleanOption(key, val));
  }
}

Box Context::Impl::ExtractModel(const Box& box) const {
  if (static_cast<int>(model_variables_.size()) == box.size()) {
    // Every variable is a model variable. Simply return the @p box.
    return box;
  }
  Box new_box;
  for (const Variable& v : box.variables()) {
    if (is_model_variable(v)) {
      new_box.Add(v, box[v].lb(), box[v].ub());
    }
  }
  return new_box;
}

bool Context::Impl::is_model_variable(const Variable& v) const {
  return (model_variables_.find(v.get_id()) != model_variables_.end());
}

void Context::Impl::mark_model_variable(const Variable& v) {
  model_variables_.insert(v.get_id());
}

const ScopedVector<Formula>& Context::Impl::assertions() const {
  return stack_;
}

}  // namespace dreal
