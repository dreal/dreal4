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

#include <vector>

#include "dreal/contractor/contractor_cell.h"
#include "dreal/util/box.h"

namespace dreal {

// Contractor for integer variables. For an integer variable `i = [lb,
// ub]`, it reduces the assignment into `[ceil(lb), floor(ub)]`.
//
// This class should be created via `make_contractor_integer` which
// handles the case where there is no integer/binary variables in a
// box.
class ContractorInteger : public ContractorCell {
 public:
  ContractorInteger(const Box& box, const Config& config);

  /// Deleted copy constructor.
  ContractorInteger(const ContractorInteger&) = delete;

  /// Deleted move constructor.
  ContractorInteger(ContractorInteger&&) = delete;

  /// Deleted copy assign operator.
  ContractorInteger& operator=(const ContractorInteger&) = delete;

  /// Deleted move assign operator.
  ContractorInteger& operator=(ContractorInteger&&) = delete;

  /// Default destructor.
  ~ContractorInteger() override = default;

  void Prune(ContractorStatus* contractor_status) const override;
  std::ostream& display(std::ostream& os) const override;

 private:
  std::vector<int> int_indexes_;
};
}  // namespace dreal
