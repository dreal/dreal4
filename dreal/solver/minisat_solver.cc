#include "dreal/solver/sat_solver.h"

#include "dreal/util/logging.h"

namespace dreal {

using std::experimental::optional;
using std::experimental::make_optional;
using std::vector;

SatSolver::SatSolver(Cnfizer* const cnfizer,
                     PredicateAbstractor* const predicate_abstractor)
    : cnfizer_{*cnfizer}, predicate_abstractor_{*predicate_abstractor} {}

SatSolver::SatSolver(Cnfizer* const cnfizer,
                     PredicateAbstractor* const predicate_abstractor,
                     const vector<Formula>& clauses)
    : SatSolver{cnfizer, predicate_abstractor} {
  AddClauses(clauses);
}

void SatSolver::Reset() { sat_ = std::make_shared<Minisat::Solver>(); }

void SatSolver::AddFormula(const Formula& f) {
  AddClauses(cnfizer_.Convert(predicate_abstractor_.Convert(f)));
}

void SatSolver::AddClauses(const vector<Formula>& formulas) {
  for (const Formula& f : formulas) {
    AddClause(f);
  }
}

void SatSolver::AddClause(const Formula& f) {
  // Set up Variable ⇔ Literal (in SAT) map.
  for (const Variable& var : f.GetFreeVariables()) {
    MakeSatVar(var);
  }
  // Add clauses to SAT solver.

  // TODO(soonho): do the allocation here.
  Minisat::vec<Minisat::Lit> clause;
  DoAddClause(f, &clause);
}

optional<vector<Formula>> SatSolver::CheckSat() {
  // Call SAT solver.
  const bool ret{sat_->solve()};
  if (ret) {
    // SAT Case.
    vector<Formula> ret;
    const auto& model{sat_->model};
    const auto& var_to_formula{predicate_abstractor_.var_to_formula_map()};

    // assert(model.size() == next_lit_);

    for (int i = 0; i < model.size(); ++i) {
      if (model[i] == Minisat::l_Undef) {
        continue;
      }
      const Variable& var{to_sym_var_[i]};
      auto it = var_to_formula.find(var);
      if (it != var_to_formula.end()) {
        const Formula& f{it->second};
        if (model[i] == Minisat::l_True) {
          ret.push_back(f);
        } else {
          ret.push_back(!f);
        }
      }
    }
    return make_optional(ret);
  } else {
    // UNSAT Case.
    return {};
  }
}

void SatSolver::AddLiteral(const Formula& f,
                           Minisat::vec<Minisat::Lit>* clause) {
  assert(is_variable(f) || (is_negation(f) && is_variable(get_operand(f))));
  if (is_variable(f)) {
    // f = b
    const Variable& var{get_variable(f)};
    assert(var.get_type() == Variable::Type::BOOLEAN);
    // Add l = b
    clause->push(Minisat::mkLit(to_sat_var_[var], false));
  } else {
    // f = ¬b
    assert(is_negation(f) && is_variable(get_operand(f)));
    const Variable& var{get_variable(get_operand(f))};
    assert(var.get_type() == Variable::Type::BOOLEAN);
    // Add l = ¬b
    clause->push(Minisat::mkLit(to_sat_var_[var], true));
  }
}

void SatSolver::DoAddClause(const Formula& f,
                            Minisat::vec<Minisat::Lit>* clause) {
  if (is_disjunction(f)) {
    // f = l₁ ∨ ... ∨ lₙ
    for (const Formula& l : get_operands(f)) {
      AddLiteral(l, clause);
    }
  } else {
    // f = b or f = ¬b.
    AddLiteral(f, clause);
  }
  sat_->addClause(*clause);
}

void SatSolver::MakeSatVar(const Variable& var) {
  auto it = to_sat_var_.find(var);
  if (it != to_sat_var_.end()) {
    // Found.
    return;
  }
  // It's not in the maps, let's make one and add it.
  const Minisat::Var sat_var{sat_->newVar()};
  to_sat_var_.emplace_hint(it, var, sat_var);
  to_sym_var_.emplace(sat_var, var);
  // std::cerr << var << " " << predicate_abstractor_.var_to_formula_map()[var]
  //           << " " << to_sat_var_.size() << "\n";

  return;
}

}  // namespace dreal
