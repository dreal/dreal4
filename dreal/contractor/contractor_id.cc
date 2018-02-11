#include "dreal/contractor/contractor_id.h"

using std::ostream;

namespace dreal {
ContractorId::ContractorId(const Config& config)
    : ContractorCell{Contractor::Kind::ID,
                     ibex::BitSet::empty(1) /* this is meaningless */, config} {
}

void ContractorId::Prune(ContractorStatus*) const {
  // No op.
}
ostream& ContractorId::display(ostream& os) const { return os << "ID()"; }

}  // namespace dreal
