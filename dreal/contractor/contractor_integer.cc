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
#include "dreal/contractor/contractor_integer.h"

#include <cmath>

#include "dreal/util/assert.h"
#include "dreal/util/math.h"

using std::ostream;

namespace dreal {

ContractorInteger::ContractorInteger(const Box& box, const Config& config)
    : ContractorCell{Contractor::Kind::INTEGER, DynamicBitset(box.size()),
                     config} {
  DynamicBitset& input{mutable_input()};
  int_indexes_.reserve(box.size());
  for (int i = 0; i < box.size(); ++i) {
    const Variable::Type type{box.variable(i).get_type()};
    if (type == Variable::Type::INTEGER || type == Variable::Type::BINARY) {
      int_indexes_.push_back(i);
      input.set(i);
    }
  }
  DREAL_ASSERT(!int_indexes_.empty());
}

void ContractorInteger::Prune(ContractorStatus* contractor_status) const {
  Box& box{contractor_status->mutable_box()};
  for (const int idx : int_indexes_) {
    Box::Interval& iv{box[idx]};
    if (iv.is_empty()) {
      continue;
    }
    if (!is_integer(iv.lb()) || !is_integer(iv.ub())) {
      const double new_lb{std::ceil(iv.lb())};
      const double new_ub{std::floor(iv.ub())};
      if (new_lb <= new_ub) {
        iv = Box::Interval{new_lb, new_ub};
        contractor_status->mutable_output().set(idx);
      } else {
        // [new_lb, new_ub] = empty
        box.set_empty();
        contractor_status->AddUnsatWitness(box.variable(idx));
        contractor_status->mutable_output().set();
        return;
      }
    }
  }
}

ostream& ContractorInteger::display(ostream& os) const {
  return os << "Integer()";
}

}  // namespace dreal
