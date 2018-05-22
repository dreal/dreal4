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
  // Build forall_vec_ (of vector<Variable>).
  for (const Variable& var : forall_variables_) {
    forall_vec_.push_back(var);
  }

  // 1. Filter bound constraints.
  Box box{forall_vec_};
  vector<Formula> formulas;
  if (is_conjunction(query)) {
    formulas.reserve(get_operands(query).size());
    for (const Formula& f : get_operands(query)) {
      DREAL_ASSERT(is_relational(f));
      const FilterAssertionResult result{FilterAssertion(f, &box)};
      if (result == FilterAssertionResult::NotFiltered) {
        formulas.push_back(f);
      }
    }
  } else {
    DREAL_ASSERT(is_relational(query));
    const FilterAssertionResult result{FilterAssertion(query, &box)};
    if (result == FilterAssertionResult::NotFiltered) {
      formulas.push_back(query);
    }
  }
  if (formulas.empty()) {
    // This will leave opt_ as nullptr. `Refine(box)` will return box then.
    DREAL_ASSERT(!opt_);
    return;
  }

  // 2. Build an Nlopt problem by adding constraints and setting up an
  // objective function.
  if (IsDifferentiable(query)) {
    // See https://nlopt.readthedocs.io/en/latest/NLopt_Algorithms/#slsqp
    opt_ = make_unique<NloptOptimizer>(nlopt::algorithm::LD_SLSQP, box, config);
  } else {
    // See
    // http://nlopt.readthedocs.io/en/latest/NLopt_Algorithms/#cobyla-constrained-optimization-by-linear-approximations
    opt_ =
        make_unique<NloptOptimizer>(nlopt::algorithm::LN_COBYLA, box, config);
  }
  Expression objective{};
  for (const Formula& f : formulas) {
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
  if (!opt_) {
    return box;
  }

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
    const nlopt::result result = opt_->Optimize(&init_, &optimal_value, env);
    switch (result) {
      case nlopt::result::FAILURE:
        DREAL_LOG_ERROR("LOCAL OPT FAILED: nlopt error-code {}", "FAILURE");
        break;
      case nlopt::result::INVALID_ARGS:
        DREAL_LOG_ERROR("LOCAL OPT FAILED: nlopt error-code {}",
                        "INVALID_ARGS");
        break;
      case nlopt::result::OUT_OF_MEMORY:
        DREAL_LOG_ERROR("LOCAL OPT FAILED: nlopt error-code {}",
                        "OUT_OF_MEMORY");
        break;
      case nlopt::result::FORCED_STOP:
        DREAL_LOG_ERROR("LOCAL OPT FAILED: nlopt error-code {}", "FORCED_STOP");
        break;
      case nlopt::result::SUCCESS:
      case nlopt::result::STOPVAL_REACHED:
      case nlopt::result::FTOL_REACHED:
      case nlopt::result::XTOL_REACHED:
      case nlopt::result::MAXEVAL_REACHED:
      case nlopt::result::MAXTIME_REACHED:
      case nlopt::result::ROUNDOFF_LIMITED:
        // 3. move the solution values from x into box.
        i = 0;
        for (const Variable& var : forall_vec_) {
          box[var] = init_[i++];
        }
    }
    return box;
  } catch (std::exception& e) {
    DREAL_LOG_DEBUG("LOCAL OPT FAILED: Exception {}", e.what());
    return box;
  }
}
}  // namespace dreal
