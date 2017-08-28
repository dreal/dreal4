#pragma once

#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/util/box.h"
#include "dreal/util/evaluator.h"
#include "dreal/util/symbolic.h"

namespace dreal {

class Icp {
 public:
  enum class Status {
    UNCHECKED,
    SAT,
    UNSAT,
  };

  Icp(Contractor contractor, std::vector<Evaluator> evaluators,
      double precision);
  bool CheckSat(ContractorStatus* cs);

 private:
  const Contractor contractor_;
  std::vector<Evaluator> evaluators_;
  const double precision_{};
};

}  // namespace dreal
