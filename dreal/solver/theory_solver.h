#pragma once

#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/solver/config.h"
#include "dreal/util/box.h"
#include "dreal/util/evaluator.h"
#include "dreal/util/symbolic.h"

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
  const std::set<Formula>& GetUsedConstraints() const;

 private:
  Contractor BuildContractor(const std::vector<Formula>& assertions);
  std::vector<Evaluator> BuildEvaluator(const std::vector<Formula>& assertions);

  const Config& config_;
  const Box& box_;
  Status status_{Status::UNCHECKED};
  ContractorStatus contractor_status_;
  // const Nnfizer nnfizer_;

  std::unordered_map<Formula, Contractor, hash_value<Formula>>
      ibex_contractor_cache_;
  std::unordered_map<Formula, Evaluator, hash_value<Formula>> evaluator_cache_;

  // stat
  int num_check_sat{0};
};

}  // namespace dreal
