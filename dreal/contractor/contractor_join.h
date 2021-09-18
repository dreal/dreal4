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

/// Join contractor.
/// (C₁ ∨ ... ∨ Cₙ)(b) = C₁(b) ∨ ... ∨ Cₙ(b).
class ContractorJoin : public ContractorCell {
 public:
  /// Deletes default constructor.
  ContractorJoin() = delete;

  /// Constructs a join contractor from a {C₁, ..., Cₙ}.
  ContractorJoin(std::vector<Contractor> contractors, const Config& config);

  /// Deleted copy constructor.
  ContractorJoin(const ContractorJoin&) = delete;

  /// Deleted move constructor.
  ContractorJoin(ContractorJoin&&) = delete;

  /// Deleted copy assign operator.
  ContractorJoin& operator=(const ContractorJoin&) = delete;

  /// Deleted move assign operator.
  ContractorJoin& operator=(ContractorJoin&&) = delete;

  /// Default destructor.
  ~ContractorJoin() override = default;

  void Prune(ContractorStatus* cs) const override;
  std::ostream& display(std::ostream& os) const override;

 private:
  std::vector<Contractor> contractors_;
};
}  // namespace dreal
