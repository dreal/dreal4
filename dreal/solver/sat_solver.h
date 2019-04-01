#pragma once

#include <memory>
#include <set>
#include <utility>
#include <vector>

#include "./picosat.h"

#include "dreal/solver/config.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/optional.h"
#include "dreal/util/predicate_abstractor.h"
#include "dreal/util/scoped_unordered_map.h"
#include "dreal/util/scoped_unordered_set.h"
#include "dreal/util/tseitin_cnfizer.h"

namespace dreal {

class SatSolver {
 public:
  using Literal = std::pair<Variable, bool>;

  // Boolean model + Theory model.
  using Model = std::pair<std::vector<Literal>, std::vector<Literal>>;

  /// Constructs a SatSolver.
  explicit SatSolver(const Config& config);

  /// Constructs a SatSolver while asserting @p clauses.
  SatSolver(const Config& config, const std::vector<Formula>& clauses);

  /// Deleted copy constructor.
  SatSolver(const SatSolver&) = delete;

  /// Deleted move constructor.
  SatSolver(SatSolver&&) = delete;

  /// Deleted copy-assignment operator.
  SatSolver& operator=(const SatSolver&) = delete;

  /// Deleted move-assignment operator.
  SatSolver& operator=(SatSolver&&) = delete;

  ~SatSolver();

  /// Adds a formula @p f to the solver.
  ///
  /// @note If @p f is a clause, please use AddClause function. This
  /// function does not assume anything about @p f and perform
  /// pre-processings (CNFize and PredicateAbstraction).
  void AddFormula(const Formula& f);

  /// Adds formulas @p formulas to the solver.
  void AddFormulas(const std::vector<Formula>& formulas);

  /// Given a @p formulas = {f₁, ..., fₙ}, adds a clause (¬f₁ ∨ ... ∨ ¬ fₙ) to
  /// the solver.
  void AddLearnedClause(const std::set<Formula>& formulas);

  /// Checks the satisfiability of the current configuration.
  ///
  /// @returns a witness, satisfying model if the problem is satisfiable.
  /// @returns nullopt if UNSAT.
  optional<Model> CheckSat();

  // TODO(soonho): Push/Pop cnfizer and predicate_abstractor?
  void Pop();

  void Push();

  Formula theory_literal(const Variable& var) const {
    return predicate_abstractor_[var];
  }

 private:
  // Adds a formula @p f to the solver.
  //
  // @pre @p f is a clause. That is, it is either a literal (b or ¬b)
  // or a disjunction of literals (l₁ ∨ ... ∨ lₙ).
  void AddClause(const Formula& f);

  // Adds a vector of formulas @p formulas to the solver.
  //
  // @pre Each formula fᵢ ∈ formulas is a clause.
  void AddClauses(const std::vector<Formula>& formulas);

  // Returns a corresponding literal ID of @p var. It maintains two
  // maps `lit_to_var_` and `var_to_lit_` to keep track of the
  // relationship between Variable ⇔ Literal (in SAT).
  void MakeSatVar(const Variable& var);

  // Add a symbolic formula @p f to @p clause.
  //
  // @pre @p f is either a Boolean variable or a negation of Boolean
  // variable.
  void AddLiteral(const Formula& f);

  // Add a clause @p f to sat solver.
  void DoAddClause(const Formula& f);

  // Member variables
  // ----------------
  // Pointer to the PicoSat solver.
  PicoSAT* const sat_{};
  TseitinCnfizer cnfizer_;
  PredicateAbstractor predicate_abstractor_;

  // Map symbolic::Variable → int (Variable type in PicoSat).
  ScopedUnorderedMap<Variable::Id, int> to_sat_var_;

  // Map int (Variable type in PicoSat) → symbolic::Variable.
  ScopedUnorderedMap<int, Variable> to_sym_var_;

  /// Set of temporary Boolean variables introduced by Tseitin
  /// transformations.
  ScopedUnorderedSet<Variable::Id> tseitin_variables_;

  /// @note We found an issue when picosat_deref_partial is used with
  /// picosat_pop. When this variable is true, we use `picosat_deref`
  /// instead.
  ///
  /// TODO(soonho): Remove this hack when it's not needed.
  bool has_picosat_pop_used_{false};
};

}  // namespace dreal
