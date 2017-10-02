#include "dreal/solver/evaluator_forall.h"

#include <set>
#include <utility>
#include <experimental/optional>

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/exception.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::experimental::optional;
using std::ostream;
using std::set;
using std::vector;

namespace {
// Returns vars₁ ∪ vars₂.
vector<Variable> Add(vector<Variable> vars1, const Variables& vars2) {
  vars1.insert(vars1.begin(), vars2.begin(), vars2.end());
  return vars1;
}

// Given f = [(e₁(x, y) ≥ 0) ∨ ... ∨ (eₙ(x, y) ≥ 0)], build an
// evaluator for each (eᵢ(x, y) ≥ 0) and return a vector of
// evaluators.
vector<EvaluatorQuantifierFree> BuildEvaluators(
    const Formula& f, const vector<Variable>& variables) {
  DREAL_LOG_DEBUG("BuildEvaluators");
  const Formula& quantified_formula{get_quantified_formula(f)};
  assert(is_clause(quantified_formula));
  const set<Formula>& disjuncts{get_operands(quantified_formula)};
  vector<EvaluatorQuantifierFree> evaluators;
  evaluators.reserve(disjuncts.size());
  for (const Formula& disjunct : disjuncts) {
    evaluators.emplace_back(disjunct, variables);
  }
  return evaluators;
}

}  // namespace

EvaluatorForall::EvaluatorForall(const Formula& f,
                                 const vector<Variable>& variables,
                                 const double epsilon, const double delta)
    : f_{f},
      evaluators_{
          BuildEvaluators(f_, Add(variables, get_quantified_variables(f)))} {
  DREAL_LOG_DEBUG("EvaluatorForall({})", f);
  context_.mutable_config().mutable_precision() = delta;
  for (const Variable& exist_var : variables) {
    context_.DeclareVariable(exist_var);
  }
  for (const Variable& forall_var : get_quantified_variables(f)) {
    context_.DeclareVariable(forall_var);
  }
  context_.Assert(DeltaStrengthen(!get_quantified_formula(f), epsilon));
}

EvaluatorForall::~EvaluatorForall() {
  DREAL_LOG_DEBUG("EvaluatorForall()::~EvaluatorForall()");
}

EvaluationResult EvaluatorForall::operator()(const Box& box) const {
  for (const Variable& v : box.variables()) {
    context_.SetInterval(v, box[v].lb(), box[v].ub());
  }
  optional<Box> counterexample = context_.CheckSat();
  DREAL_LOG_DEBUG("EvaluatorForall::operator({})", box);
  if (counterexample) {
    DREAL_LOG_DEBUG("EvaluatorForall::operator()  --  CE found: ",
                    *counterexample);
    for (const Variable& exist_var : box.variables()) {
      (*counterexample)[exist_var] = box[exist_var];
    }
    double max_diam = 0.0;
    for (const EvaluatorQuantifierFree& evaluator : evaluators_) {
      const EvaluationResult eval_result = evaluator(*counterexample);
      if (eval_result.type() == EvaluationResult::Type::UNSAT) {
        continue;
      }
      const double diam_i{eval_result.evaluation().diam()};
      if (diam_i > max_diam) {
        max_diam = diam_i;
      }
    }
    return EvaluationResult{EvaluationResult::Type::UNKNOWN,
                            Box::Interval(0.0, max_diam)};
  } else {
    DREAL_LOG_DEBUG("EvaluatorForall::operator()  --  No CE found: ");
    return EvaluationResult{EvaluationResult::Type::VALID,
                            Box::Interval(0.0, 0.0)};
  }
}

ostream& EvaluatorForall::Display(ostream& os) const {
  return os << "Evaluator(" << f_ << ")";
}

}  // namespace dreal
