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
#include <ostream>

#include "./ibex.h"

#include "dreal/contractor/contractor_cell.h"
#include "dreal/contractor/contractor_status.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/ibex_converter.h"

namespace dreal {

/// Contractor class wrapping IBEX's forward/backward contractor.
class ContractorIbexFwdbwd : public ContractorCell {
 public:
  /// Deleted default constructor.
  ContractorIbexFwdbwd() = delete;

  /// Constructs IbexFwdbwd contractor using @p f and @p box.
  ContractorIbexFwdbwd(Formula f, const Box& box, const Config& config);

  /// Deleted copy constructor.
  ContractorIbexFwdbwd(const ContractorIbexFwdbwd&) = delete;

  /// Deleted move constructor.
  ContractorIbexFwdbwd(ContractorIbexFwdbwd&&) = delete;

  /// Deleted copy assign operator.
  ContractorIbexFwdbwd& operator=(const ContractorIbexFwdbwd&) = delete;

  /// Deleted move assign operator.
  ContractorIbexFwdbwd& operator=(ContractorIbexFwdbwd&&) = delete;

  ~ContractorIbexFwdbwd() override = default;

  void Prune(ContractorStatus* cs) const override;

  std::ostream& display(std::ostream& os) const override;

  /// Returns true if it has no internal ibex contractor.
  bool is_dummy() const;

 private:
  const Formula f_;
  bool is_dummy_{false};
  IbexConverter ibex_converter_;
  std::unique_ptr<const ibex::ExprCtr> expr_ctr_;
  std::unique_ptr<ibex::NumConstraint> num_ctr_;
};

}  // namespace dreal
