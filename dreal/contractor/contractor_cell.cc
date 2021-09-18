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
#include "dreal/contractor/contractor_cell.h"

#include <utility>

#include "dreal/contractor/contractor_fixpoint.h"
#include "dreal/contractor/contractor_forall.h"
#include "dreal/contractor/contractor_ibex_fwdbwd.h"
#include "dreal/contractor/contractor_ibex_polytope.h"
#include "dreal/contractor/contractor_id.h"
#include "dreal/contractor/contractor_integer.h"
#include "dreal/contractor/contractor_join.h"
#include "dreal/contractor/contractor_seq.h"
#include "dreal/contractor/contractor_worklist_fixpoint.h"
#include "dreal/util/assert.h"

using std::ostream;
using std::shared_ptr;
using std::static_pointer_cast;
using std::vector;

namespace dreal {

ContractorCell::ContractorCell(const Contractor::Kind kind, DynamicBitset input,
                               Config config)
    : kind_{kind}, input_{std::move(input)}, config_{std::move(config)} {}

Contractor::Kind ContractorCell::kind() const { return kind_; }

const DynamicBitset& ContractorCell::input() const { return input_; }

DynamicBitset& ContractorCell::mutable_input() { return input_; }

const Config& ContractorCell::config() const { return config_; }

bool ContractorCell::include_forall() const { return include_forall_; }

void ContractorCell::set_include_forall() { include_forall_ = true; }

DynamicBitset::size_type ComputeInputSize(
    const vector<Contractor>& contractors) {
  DynamicBitset::size_type ret = 0;
  for (const Contractor& c : contractors) {
    const DynamicBitset::size_type size_i = c.input().size();
    if (size_i > ret) {
      ret = size_i;
    }
  }
  return ret;
}

ostream& operator<<(ostream& os, const ContractorCell& c) {
  return c.display(os);
}

shared_ptr<ContractorId> to_id(const Contractor& contractor) {
  DREAL_ASSERT(is_id(contractor));
  return static_pointer_cast<ContractorId>(contractor.ptr_);
}
shared_ptr<ContractorInteger> to_integer(const Contractor& contractor) {
  DREAL_ASSERT(is_integer(contractor));
  return static_pointer_cast<ContractorInteger>(contractor.ptr_);
}
shared_ptr<ContractorSeq> to_seq(const Contractor& contractor) {
  DREAL_ASSERT(is_seq(contractor));
  return static_pointer_cast<ContractorSeq>(contractor.ptr_);
}
shared_ptr<ContractorIbexFwdbwd> to_ibex_fwdbwd(const Contractor& contractor) {
  DREAL_ASSERT(is_ibex_fwdbwd(contractor));
  return static_pointer_cast<ContractorIbexFwdbwd>(contractor.ptr_);
}
shared_ptr<ContractorIbexPolytope> to_ibex_polytope(
    const Contractor& contractor) {
  DREAL_ASSERT(is_ibex_polytope(contractor));
  return static_pointer_cast<ContractorIbexPolytope>(contractor.ptr_);
}
shared_ptr<ContractorFixpoint> to_fixpoint(const Contractor& contractor) {
  DREAL_ASSERT(is_fixpoint(contractor));
  return static_pointer_cast<ContractorFixpoint>(contractor.ptr_);
}
shared_ptr<ContractorWorklistFixpoint> to_worklist_fixpoint(
    const Contractor& contractor) {
  DREAL_ASSERT(is_fixpoint(contractor));
  return static_pointer_cast<ContractorWorklistFixpoint>(contractor.ptr_);
}
shared_ptr<ContractorJoin> to_join(const Contractor& contractor) {
  DREAL_ASSERT(is_join(contractor));
  return static_pointer_cast<ContractorJoin>(contractor.ptr_);
}

}  // namespace dreal
