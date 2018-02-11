#include "dreal/contractor/counterexample_refiner.h"

#include <utility>

#include "dreal/solver/filter_assertion.h"
#include "dreal/util/assert.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::make_unique;
using std::move;
using std::vector;

CounterexampleRefiner::CounterexampleRefiner(const Formula& query,
                                             Variables forall_variables,
                                             const Config& config)
    : init_(forall_variables.size(), 0.0),
      forall_variables_{move(forall_variables)} {
  DREAL_ASSERT(is_conjunction(query));

  // Build forall_vec_ (of vector<Variable>).
  for (const Variable& var : forall_variables_) {
    forall_vec_.push_back(var);
  }

  // 1. Filter bound constraints.
  Box box{forall_vec_};
  vector<Formula> formulas;
  formulas.reserve(get_operands(query).size());
  for (const Formula& f : get_operands(query)) {
    const FilterAssertionResult result{FilterAssertion(f, &box)};
    if (result == FilterAssertionResult::NotFiltered) {
      formulas.push_back(f);
    }
  }

  // 2. Build an Nlopt problem by adding constraints and setting up an
  // objective function.
  if (IsDifferentiable(query)) {
    // See https://nlopt.readthedocs.io/en/latest/NLopt_Algorithms/#slsqp
    opt_ = make_unique<NloptOptimizer>(NLOPT_LD_SLSQP, box, config);
  } else {
    // See
    // https://nlopt.readthedocs.io/en/latest/NLopt_Algorithms/#newuoa-bound-constraints
    opt_ = make_unique<NloptOptimizer>(NLOPT_LN_NEWUOA_BOUND, box, config);
  }
  Expression objective{};
  for (const Formula& f : formulas) {
    DREAL_ASSERT(is_relational(f));

    if (!f.GetFreeVariables().IsSubsetOf(forall_variables_)) {
      // F has both of exist and forall variables. We turn this into an
      // objective function.
      if (is_greater_than(f) || is_greater_than_or_equal_to(f)) {
        // f := e1 > e2  -->  e1 - e2 > 0.0
        //               -->  Maximize e1 - e2
        //               -->  Minimize e2 - e1
        const Expression& e1{get_lhs_expression(f)};
        const Expression& e2{get_rhs_expression(f)};
        objective += e2 - e1;
      } else if (is_less_than(f) || is_less_than_or_equal_to(f)) {
        // f := e1 < e2  -->  e1 - e2 < 0.0
        //               -->  Minimize e1 - e2
        const Expression& e1{get_lhs_expression(f)};
        const Expression& e2{get_rhs_expression(f)};
        objective += e1 - e2;
      } else {
        // Do nothing for equality / inequalities.
      }
    }
    // Always add it as a constraint.
    opt_->AddRelationalConstraint(f);
  }
  if (!is_zero(objective)) {
    opt_->SetMinObjective(objective);
  }
}

Box CounterexampleRefiner::Refine(Box box) {
  // 1. Set up init and env.
  Environment env;
  int i = 0;
  for (const Variable& var : box.variables()) {
    const double mid = box[var].mid();
    if (forall_variables_.include(var)) {
      init_[i++] = mid;  // forall variable
    } else {
      env.insert(var, mid);  // exist variable
    }
  }
  // 2. call optimizer
  double optimal_value{0.0};
  try {
    const nlopt_result result = opt_->Optimize(&init_, &optimal_value, env);
    if (result >= 0 || result == NLOPT_ROUNDOFF_LIMITED) {
      // 3. move the solution values from x into box.
      i = 0;
      for (const Variable& var : forall_vec_) {
        box[var] = init_[i++];
      }
    } else {
      DREAL_LOG_ERROR("LOCAL OPT FAILED: nlopt error-code {}", result);
    }
    return box;
  } catch (std::exception& e) {
    DREAL_LOG_DEBUG("LOCAL OPT FAILED: Exception {}", e.what());
    return box;
  }
}
}  // namespace dreal
