#include "dreal/solver/sat_solver.h"

#include <stdexcept>

#include "dreal/util/logging.h"

namespace dreal {

using std::experimental::make_optional;
using std::experimental::optional;
using std::runtime_error;
using std::vector;

SatSolver::SatSolver(Cnfizer* const cnfizer,
                     PredicateAbstractor* const predicate_abstractor)
    : sat_(picosat_init()),
      cnfizer_{*cnfizer},
      predicate_abstractor_{*predicate_abstractor} {}

SatSolver::SatSolver(Cnfizer* const cnfizer,
                     PredicateAbstractor* const predicate_abstractor,
                     const vector<Formula>& clauses)
    : SatSolver{cnfizer, predicate_abstractor} {
  AddClauses(clauses);
}

SatSolver::~SatSolver() {
  picosat_reset(sat_);
  DREAL_LOG_DEBUG("SatSolver::~SatSolver() #CheckSat = {}", num_of_check_sat_);
}

void SatSolver::AddFormula(const Formula& f) {
  DREAL_LOG_DEBUG("SatSolver::AddFormula({})", f);
  AddClauses(cnfizer_.Convert(predicate_abstractor_.Convert(f)));
}

void SatSolver::AddClauses(const vector<Formula>& formulas) {
  for (const Formula& f : formulas) {
    AddClause(f);
  }
}

void SatSolver::AddClause(const Formula& f) {
  DREAL_LOG_DEBUG("SatSolver::AddClause({})", f);
  // Set up Variable ⇔ Literal (in SAT) map.
  for (const Variable& var : f.GetFreeVariables()) {
    MakeSatVar(var);
  }
  // Add clauses to SAT solver.
  DoAddClause(f);
}

bool SatSolver::CheckSat() {
  DREAL_LOG_DEBUG("SatSolver::CheckSat(#vars = {}, #clauses = {})",
                  picosat_variables(sat_),
                  picosat_added_original_clauses(sat_));
  num_of_check_sat_++;
  // Call SAT solver.
  const int ret{picosat_sat(sat_, -1)};
  model_.clear();
  if (ret == PICOSAT_SATISFIABLE) {
    // SAT Case.
    const auto& var_to_formula_map = predicate_abstractor_.var_to_formula_map();
    for (int i = 1; i <= picosat_variables(sat_); ++i) {
      const int model_i{picosat_deref(sat_, i)};
      if (model_i == 0) {
        continue;
      }
      const Variable& var{to_sym_var_[i]};
      const auto it = var_to_formula_map.find(var);
      if (it != var_to_formula_map.end()) {
        if (model_i == 1) {
          model_.push_back(it->second);
        } else {
          assert(model_i == -1);
          model_.push_back(!it->second);
        }
      }
    }
    DREAL_LOG_DEBUG("SatSolver::CheckSat() Found a model.");
    return true;
  } else if (ret == PICOSAT_UNSATISFIABLE) {
    DREAL_LOG_DEBUG("SatSolver::CheckSat() No solution.");
    // UNSAT Case.
    return false;
  } else {
    assert(ret == PICOSAT_UNKNOWN);
    DREAL_LOG_CRITICAL("PICOSAT returns PICOSAT_UNKNOWN.");
    throw runtime_error("PICOSAT returns PICOSAT_UNKNOWN.");
  }
}

void SatSolver::Pop() {
  DREAL_LOG_DEBUG("SatSolver::Pop()");
  picosat_pop(sat_);
}

void SatSolver::Push() {
  DREAL_LOG_DEBUG("SatSolver::Push()");
  picosat_push(sat_);
}

void SatSolver::AddLiteral(const Formula& f) {
  assert(is_variable(f) || (is_negation(f) && is_variable(get_operand(f))));
  if (is_variable(f)) {
    // f = b
    const Variable& var{get_variable(f)};
    assert(var.get_type() == Variable::Type::BOOLEAN);
    // Add l = b
    picosat_add(sat_, to_sat_var_[var]);
  } else {
    // f = ¬b
    assert(is_negation(f) && is_variable(get_operand(f)));
    const Variable& var{get_variable(get_operand(f))};
    assert(var.get_type() == Variable::Type::BOOLEAN);
    // Add l = ¬b
    picosat_add(sat_, -to_sat_var_[var]);
  }
}

void SatSolver::DoAddClause(const Formula& f) {
  if (is_disjunction(f)) {
    // f = l₁ ∨ ... ∨ lₙ
    for (const Formula& l : get_operands(f)) {
      AddLiteral(l);
    }
  } else {
    // f = b or f = ¬b.
    AddLiteral(f);
  }
  picosat_add(sat_, 0);
}

void SatSolver::MakeSatVar(const Variable& var) {
  auto it = to_sat_var_.find(var);
  if (it != to_sat_var_.end()) {
    // Found.
    return;
  }
  // It's not in the maps, let's make one and add it.
  const int sat_var{picosat_inc_max_var(sat_)};
  to_sat_var_.emplace_hint(it, var, sat_var);
  to_sym_var_.emplace(sat_var, var);
  DREAL_LOG_DEBUG("SatSolver::MakeSatVar({} ↦ {})", var, sat_var);
  return;
}
}  // namespace dreal
