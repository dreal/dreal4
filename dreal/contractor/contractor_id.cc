#include "dreal/contractor/contractor_id.h"

using std::ostream;

namespace dreal {
void ContractorId::Prune(ContractorStatus*) const {
  // No op.
}
ostream& ContractorId::display(ostream& os) const { return os << "ID()"; }

}  // namespace dreal
