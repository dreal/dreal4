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

#include "dreal/contractor/contractor_cell.h"

namespace dreal {

class ContractorId : public ContractorCell {
 public:
  /// Constructs ID contractor.
  explicit ContractorId(const Config& config);

  /// Deleted copy constructor.
  ContractorId(const ContractorId&) = delete;

  /// Deleted move constructor.
  ContractorId(ContractorId&&) = delete;

  /// Deleted copy assign operator.
  ContractorId& operator=(const ContractorId&) = delete;

  /// Deleted move assign operator.
  ContractorId& operator=(ContractorId&&) = delete;

  /// Default destructor.
  ~ContractorId() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;
};
}  // namespace dreal
