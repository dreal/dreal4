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

#include <ostream>
#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_cell.h"

namespace dreal {

/// Sequential contractor: Sequentially apply C₁, ..., Cₙ.
class ContractorSeq : public ContractorCell {
 public:
  /// Delete default constructor.
  ContractorSeq() = delete;

  /// Constructor a sequential contractor from a {C₁, ..., Cₙ}.
  ContractorSeq(std::vector<Contractor> contractors, const Config& config);

  /// Deleted copy constructor.
  ContractorSeq(const ContractorSeq&) = delete;

  /// Deleted move constructor.
  ContractorSeq(ContractorSeq&&) = delete;

  /// Deleted copy assign operator.
  ContractorSeq& operator=(const ContractorSeq&) = delete;

  /// Deleted move assign operator.
  ContractorSeq& operator=(ContractorSeq&&) = delete;

  /// Default destructor.
  ~ContractorSeq() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

  const std::vector<Contractor>& contractors() const;

 private:
  std::vector<Contractor> contractors_;
};
}  // namespace dreal
