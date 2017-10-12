#pragma once

#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/solver/config.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

class TheorySolver {
 public:
  enum class Status {
    UNCHECKED,
    SAT,
    UNSAT,
  };

  TheorySolver() = delete;
  TheorySolver(const Config& config, const Box& box);
  ~TheorySolver();

  /// Checks consistency. Returns true if there is a satisfying
  /// assignment. Otherwise, return false.
  ///
  /// @note It does the real-work only if status_ is UNCHECKED. Otherwise, it
  /// does nothing.
  bool CheckSat(const std::vector<Formula>& assertions);

  /// Gets a satisfying Model.
  ///
  /// @pre status_ is SAT.
  Box GetModel() const;

  /// Gets a list of used constraints.
  /// @pre status_ is UNSAT.
  const std::unordered_set<Formula, hash_value<Formula>> GetExplanation() const;

 private:
  Contractor BuildContractor(const std::vector<Formula>& assertions);
  std::vector<FormulaEvaluator> BuildFormulaEvaluator(
      const std::vector<Formula>& assertions);

  const Config& config_;
  const Box& box_;
  Status status_{Status::UNCHECKED};
  ContractorStatus contractor_status_;
  // const Nnfizer nnfizer_;

  std::unordered_map<Formula, Contractor, hash_value<Formula>>
      contractor_cache_;
  std::unordered_map<Formula, FormulaEvaluator, hash_value<Formula>>
      formula_evaluator_cache_;

  // stat
  int num_check_sat{0};
};

}  // namespace dreal
