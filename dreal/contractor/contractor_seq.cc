#include "dreal/contractor/contractor_seq.h"

#include <utility>

#include "dreal/util/assert.h"

using std::move;
using std::ostream;
using std::vector;

namespace dreal {

ContractorSeq::ContractorSeq(vector<Contractor> contractors,
                             const Config& config)
    : ContractorCell{Contractor::Kind::SEQ,
                     ibex::BitSet::empty(ComputeInputSize(contractors)),
                     config},
      contractors_{move(contractors)} {
  DREAL_ASSERT(!contractors_.empty());
  ibex::BitSet& input{mutable_input()};
  for (const Contractor& c : contractors_) {
    input |= c.input();
  }
}

void ContractorSeq::Prune(ContractorStatus* cs) const {
  for (const Contractor& c : contractors_) {
    c.Prune(cs);
    if (cs->box().empty()) {
      return;
    }
  }
}

ostream& ContractorSeq::display(ostream& os) const {
  os << "Seq(";
  for (const Contractor& c : contractors_) {
    os << c << ", ";
  }
  return os << ")";
}

const std::vector<Contractor>& ContractorSeq::contractors() const {
  return contractors_;
}

}  // namespace dreal
