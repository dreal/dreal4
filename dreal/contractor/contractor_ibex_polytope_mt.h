/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
#pragma once

#include <memory>
#include <mutex>
#include <ostream>
#include <vector>

#include "dreal/contractor/contractor_cell.h"
#include "dreal/contractor/contractor_ibex_polytope.h"
#include "dreal/contractor/contractor_status.h"
#include "dreal/solver/config.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

/// Multi-thread version of ContractorIbexFwdbwd contractor.
///
/// The base ContractorIbexPolytope is not thread-safe. When there are N jobs,
/// it creates N ContractorIbexPolytope instances internally and make sure that
/// each thread calls a designated instance.
class ContractorIbexPolytopeMt : public ContractorCell {
 public:
  /// Constructs IbexPolytopeMt contractor using @p f and @p vars.
  ContractorIbexPolytopeMt(std::vector<Formula> formulas, const Box& box,
                           const Config& config);

  /// Deleted copy constructor.
  ContractorIbexPolytopeMt(const ContractorIbexPolytopeMt&) = delete;

  /// Deleted move constructor.
  ContractorIbexPolytopeMt(ContractorIbexPolytopeMt&&) = delete;

  /// Deleted copy assign operator.
  ContractorIbexPolytopeMt& operator=(const ContractorIbexPolytopeMt&) = delete;

  /// Deleted move assign operator.
  ContractorIbexPolytopeMt& operator=(ContractorIbexPolytopeMt&&) = delete;

  /// Default destructor.
  ~ContractorIbexPolytopeMt() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

  /// Returns true if it has no internal ibex contractor.
  bool is_dummy() const;

 private:
  ContractorIbexPolytope* GetCtcOrCreate(const Box& box) const;
  bool is_dummy_{false};

  const std::vector<Formula> formulas_;
  const Config config_;

  // ctc_ready_[i] is 1 indicates that ctcs_[i] is ready to be used.
  mutable std::vector<int> ctc_ready_;
  mutable std::vector<std::unique_ptr<ContractorIbexPolytope>> ctcs_;
};

}  // namespace dreal
