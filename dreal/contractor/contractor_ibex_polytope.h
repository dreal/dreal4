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
#include <vector>

#include "./ibex.h"

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_cell.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/ibex_converter.h"

namespace dreal {

// Custom deleter for ibex::ExprCtr. It deletes the internal
// ibex::ExprNode while keeping the ExprSymbols intact. Note that the
// ExprSymbols will be deleted separately in
// ~ContractorIbexPolytope().
struct ExprCtrDeleter {
  void operator()(const ibex::ExprCtr* const p) const {
    if (p) {
      ibex::cleanup(p->e, false);
      delete p;
    }
  }
};

class ContractorIbexPolytope : public ContractorCell {
 public:
  /// Constructs IbexPolytope contractor using @p f and @p vars.
  ContractorIbexPolytope(std::vector<Formula> formulas, const Box& box,
                         const Config& config);

  /// Deleted copy constructor.
  ContractorIbexPolytope(const ContractorIbexPolytope&) = delete;

  /// Deleted move constructor.
  ContractorIbexPolytope(ContractorIbexPolytope&&) = delete;

  /// Deleted copy assign operator.
  ContractorIbexPolytope& operator=(const ContractorIbexPolytope&) = delete;

  /// Deleted move assign operator.
  ContractorIbexPolytope& operator=(ContractorIbexPolytope&&) = delete;

  /// Default destructor.
  ~ContractorIbexPolytope() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

  /// Returns true if it has no internal ibex contractor.
  bool is_dummy() const;

 private:
  const std::vector<Formula> formulas_;
  bool is_dummy_{false};

  IbexConverter ibex_converter_;
  std::unique_ptr<ibex::SystemFactory> system_factory_;
  std::unique_ptr<ibex::System> system_;
  std::unique_ptr<ibex::LinearizerCombo> linear_relax_combo_;
  std::unique_ptr<ibex::CtcPolytopeHull> ctc_;
  std::vector<std::unique_ptr<const ibex::ExprCtr, ExprCtrDeleter>> expr_ctrs_;
};

}  // namespace dreal
