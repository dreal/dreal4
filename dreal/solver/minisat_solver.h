#pragma once

#include <memory>
#include <unordered_map>
#include <vector>
#include <experimental/optional>

#include "minisat/core/Solver.h"

#include "dreal/util/cnfizer.h"
#include "dreal/util/predicate_abstractor.h"
#include "dreal/util/symbolic.h"

namespace dreal {

class SatSolver {
 public:
  /// Constructs a SatSolver using @p cnfizer and @p predicate_abstractor.
  SatSolver(Cnfizer* cnfizer, PredicateAbstractor* predicate_abstractor);

  /// Constructs a SatSolver using @p cnfizer,  @p predicate_abstractor, and @p
  /// clauses.
  SatSolver(Cnfizer* cnfizer, PredicateAbstractor* predicate_abstractor,
            const std::vector<Formula>& clauses);

  void Reset();

  /// Add a formula @p f to the solver.
  ///
  /// @note If @p f is a clause, please use AddClause function. This
  /// function does not assume anything about @p f and perform
  /// pre-processings (CNFize and PredicateAbstraction).
  void AddFormula(const Formula& f);

  /// Add a formula @p f to the solver.
  ///
  /// @pre @p f is a clause. That is, it is either a literal (b or ¬b)
  /// or a disjunction of literals (l₁ ∨ ... ∨ lₙ).
  void AddClause(const Formula& f);

  /// Add a vector of formulas @p formulas to the solver.
  ///
  /// @pre Each formula fᵢ ∈ formulas is a clause.
  void AddClauses(const std::vector<Formula>& formulas);

  /// Checks the satisfiability of the current status.
  /// If SAT, it will return a model as a list of Formula.
  /// If UNSAT, it will return an empty optional value ({}).
  std::experimental::optional<std::vector<Formula>> CheckSat();

 private:
  // Returns a corresponding literal ID of @p var. It maintains two
  // maps `lit_to_var_` and `var_to_lit_` to keep track of the
  // relationship between Variable ⇔ Literal (in SAT).
  void MakeSatVar(const Variable& var);

  // Add a symbolic formula @p f to @p clause.
  //
  // @pre @p f is either a Boolean variable or a negation of Boolean
  // variable.
  void AddLiteral(const Formula& f, Minisat::vec<Minisat::Lit>* clause);

  // Add a symbolic formula @p f to @p clause.
  //
  // @pre @p f is a clause. That is, it is either a literal (b or ¬b)
  // or a disjunction of literals (l₁ ∨ ... ∨ lₙ).
  void DoAddClause(const Formula& f, Minisat::vec<Minisat::Lit>* clause);

  std::shared_ptr<Minisat::Solver> sat_;
  Cnfizer& cnfizer_;
  PredicateAbstractor& predicate_abstractor_;
  Formula f_cnf_;

  // LitId next_lit_{0};
  // Map symbolic::Variable → Minisat::Variable (in SAT)
  std::unordered_map<Variable, Minisat::Var, hash_value<Variable>> to_sat_var_;
  // Map Minisat::Variable → symbolic::Variable
  std::unordered_map<Minisat::Var, Variable> to_sym_var_;
};

}  // namespace dreal
