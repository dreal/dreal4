#include "dreal/contractor/contractor_fixpoint.h"

#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/logging.h"

using std::move;
using std::ostream;
using std::vector;

namespace dreal {

ContractorFixpoint::ContractorFixpoint(TerminationCondition term_cond,
                                       vector<Contractor> contractors,
                                       const Config& config)
    : ContractorCell{Contractor::Kind::FIXPOINT,
                     ibex::BitSet::empty(ComputeInputSize(contractors)),
                     config},
      term_cond_{move(term_cond)},
      contractors_{move(contractors)},
      old_iv_{1 /* will be updated anyway */} {
  DREAL_ASSERT(!contractors_.empty());
  ibex::BitSet& input{mutable_input()};
  for (const Contractor& c : contractors_) {
    input |= c.input();
  }
}

void ContractorFixpoint::Prune(ContractorStatus* cs) const {
  do {
    old_iv_ = cs->box().interval_vector();
    for (const Contractor& ctc : contractors_) {
      ctc.Prune(cs);
      if (cs->box().empty()) {
        return;
      }
    }
  } while (!term_cond_(old_iv_, cs->box().interval_vector()));
}

ostream& ContractorFixpoint::display(ostream& os) const {
  os << "Fixpoint(";
  for (const Contractor& c : contractors_) {
    os << c << ", ";
  }
  return os << ")";
}

}  // namespace dreal
