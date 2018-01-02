#include "dreal/contractor/contractor_join.h"

#include <utility>
#include "dreal/util/assert.h"

using std::move;
using std::ostream;
using std::vector;

namespace dreal {

ContractorJoin::ContractorJoin(vector<Contractor> contractors)
    : ContractorCell{Contractor::Kind::JOIN,
                     ibex::BitSet::empty(ComputeInputSize(contractors))},
      contractors_{move(contractors)} {
  DREAL_ASSERT(contractors_.size() > 0);
  ibex::BitSet& input{mutable_input()};
  for (const Contractor& c : contractors_) {
    input |= c.input();
  }
}

void ContractorJoin::Prune(ContractorStatus* cs) const {
  ContractorStatus saved_original{*cs};
  cs->mutable_box().set_empty();
  for (const Contractor& contractor : contractors_) {
    ContractorStatus state_i{saved_original};
    contractor.Prune(&state_i);
    cs->InplaceJoin(state_i);
  }
}

ostream& ContractorJoin::display(ostream& os) const {
  os << "Join(";
  for (const Contractor& c : contractors_) {
    os << c << ", ";
  }
  return os << ")";
}

}  // namespace dreal
