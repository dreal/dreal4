#include "dreal/solver/sat_solver.h"

#include <ostream>

#include "dreal/util/assert.h"
#include "dreal/util/exception.h"
#include "dreal/util/logging.h"
#include "dreal/util/stat.h"
#include "dreal/util/timer.h"

namespace dreal {

using std::cout;
using std::set;
using std::vector;
using std::experimental::optional;

SatSolver::SatSolver(const Config& config) : sat_{picosat_init()} {
  // Enable partial checks via picosat_deref_partial. See the call-site in
  // SatSolver::CheckSat().
  picosat_save_original_clauses(sat_);
  if (config.random_seed() != 0) {
    picosat_set_seed(sat_, config.random_seed());
    DREAL_LOG_DEBUG("SatSolver::Set Random Seed {}", config.random_seed());
  }
  picosat_set_global_default_phase(
      sat_, static_cast<int>(config.sat_default_phase()));
  DREAL_LOG_DEBUG("SatSolver::Set Default Phase {}",
                  config.sat_default_phase());
}

SatSolver::SatSolver(const Config& config, const vector<Formula>& clauses)
    : SatSolver{config} {
  AddClauses(clauses);
}

SatSolver::~SatSolver() { picosat_reset(sat_); }

void SatSolver::AddFormula(const Formula& f) {
  DREAL_LOG_DEBUG("SatSolver::AddFormula({})", f);
  vector<Formula> clauses{cnfizer_.Convert(f)};
  // Collect Tseitin variables.
  for (const auto& p : cnfizer_.map()) {
    tseitin_variables_.insert(p.first);
  }
  for (Formula& clause : clauses) {
    clause = predicate_abstractor_.Convert(clause);
  }
  AddClauses(clauses);
}

void SatSolver::AddFormulas(const vector<Formula>& formulas) {
  for (const Formula& f : formulas) {
    AddFormula(f);
  }
}

void SatSolver::AddLearnedClause(const set<Formula>& formulas) {
  for (const Formula& f : formulas) {
    AddLiteral(!predicate_abstractor_.Convert(f));
  }
  picosat_add(sat_, 0);
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

namespace {
class SatSolverStat : public Stat {
 public:
  explicit SatSolverStat(const bool enabled) : Stat{enabled} {};
  SatSolverStat(const SatSolverStat&) = default;
  SatSolverStat(SatSolverStat&&) = default;
  SatSolverStat& operator=(const SatSolverStat&) = default;
  SatSolverStat& operator=(SatSolverStat&&) = default;
  ~SatSolverStat() override {
    if (enabled()) {
      using fmt::print;
      print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of CheckSat",
            "SAT level", num_check_sat_);
      print(cout, "{:<45} @ {:<20} = {:>15f} sec\n",
            "Total time spent in SAT checks", "SAT level",
            timer_check_sat_.seconds());
    }
  }

  int num_check_sat_{0};
  Timer timer_check_sat_;
};
}  // namespace

std::experimental::optional<SatSolver::Model> SatSolver::CheckSat() {
  static SatSolverStat stat{DREAL_LOG_INFO_ENABLED};
  DREAL_LOG_DEBUG("SatSolver::CheckSat(#vars = {}, #clauses = {})",
                  picosat_variables(sat_),
                  picosat_added_original_clauses(sat_));
  stat.num_check_sat_++;
  // Call SAT solver.
  TimerGuard check_sat_timer_guard(&stat.timer_check_sat_,
                                   DREAL_LOG_INFO_ENABLED);
  const int ret{picosat_sat(sat_, -1)};
  check_sat_timer_guard.pause();

  Model model;
  auto& boolean_model = model.first;
  auto& theory_model = model.second;
  if (ret == PICOSAT_SATISFIABLE) {
    // SAT Case.
    const auto& var_to_formula_map = predicate_abstractor_.var_to_formula_map();
    for (int i = 1; i <= picosat_variables(sat_); ++i) {
      const int model_i{picosat_deref_partial(sat_, i)};
      if (model_i == 0) {
        continue;
      }
      const Variable& var{to_sym_var_[i]};
      const auto it = var_to_formula_map.find(var);
      if (it != var_to_formula_map.end()) {
        DREAL_LOG_TRACE("SatSolver::CheckSat: Add theory literal {}{} to Model",
                        model_i ? "" : "¬", var);
        theory_model.emplace_back(var, model_i == 1);
      } else if (tseitin_variables_.find(var) == tseitin_variables_.end()) {
        DREAL_LOG_TRACE(
            "SatSolver::CheckSat: Add Boolean literal {}{} to Model ",
            model_i ? "" : "¬", var);
        boolean_model.emplace_back(var, model_i == 1);
      } else {
        DREAL_LOG_TRACE(
            "SatSolver::CheckSat: Skip {}{} which is a temporary variable.",
            model_i ? "" : "¬", var);
      }
    }
    DREAL_LOG_DEBUG("SatSolver::CheckSat() Found a model.");
    return model;
  } else if (ret == PICOSAT_UNSATISFIABLE) {
    DREAL_LOG_DEBUG("SatSolver::CheckSat() No solution.");
    // UNSAT Case.
    return {};
  } else {
    DREAL_ASSERT(ret == PICOSAT_UNKNOWN);
    DREAL_LOG_CRITICAL("PICOSAT returns PICOSAT_UNKNOWN.");
    throw DREAL_RUNTIME_ERROR("PICOSAT returns PICOSAT_UNKNOWN.");
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
  DREAL_ASSERT(is_variable(f) ||
               (is_negation(f) && is_variable(get_operand(f))));
  if (is_variable(f)) {
    // f = b
    const Variable& var{get_variable(f)};
    DREAL_ASSERT(var.get_type() == Variable::Type::BOOLEAN);
    // Add l = b
    picosat_add(sat_, to_sat_var_[var]);
  } else {
    // f = ¬b
    DREAL_ASSERT(is_negation(f) && is_variable(get_operand(f)));
    const Variable& var{get_variable(get_operand(f))};
    DREAL_ASSERT(var.get_type() == Variable::Type::BOOLEAN);
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
}
}  // namespace dreal
