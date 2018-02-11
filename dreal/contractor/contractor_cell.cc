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

ContractorCell::ContractorCell(const Contractor::Kind kind,
                               const ibex::BitSet& input, const Config& config)
    : kind_{kind}, input_{input}, config_{config} {}

Contractor::Kind ContractorCell::kind() const { return kind_; }

const ibex::BitSet& ContractorCell::input() const { return input_; }

ibex::BitSet& ContractorCell::mutable_input() { return input_; }

const Config& ContractorCell::config() const { return config_; }

// Returns max(c₁.input().max(), ..., cₙ.input().max()).
// This is used in ContractorSeq, ContractorFixpoint, and
// ContractorWorklistFixpoint to find the size of its input BitSet.
int ComputeInputSize(const vector<Contractor>& contractors) {
  int ret = 0;
  for (const Contractor& c : contractors) {
    // When c.input().empty(), c.input().max() has INT_MAX so we need to skip
    // it.
    if (!c.input().empty()) {
      const int max_i = c.input().max();
      if (max_i > ret) {
        ret = max_i;
      }
    }
  }
  return ret + 1;
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
