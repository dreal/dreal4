#include "dreal/contractor/contractor_fixpoint.h"

#include <utility>

#include "dreal/util/logging.h"

using std::move;
using std::ostream;
using std::vector;

namespace dreal {

ContractorFixpoint::ContractorFixpoint(TerminationCondition term_cond,
                                       vector<Contractor> contractors)
    : ContractorCell{ibex::BitSet::empty(ComputeInputSize(contractors))},
      term_cond_{move(term_cond)},
      contractors_{move(contractors)} {
  assert(contractors_.size() > 0);
  ibex::BitSet& input{get_mutable_input()};
  for (const Contractor& c : contractors_) {
    input |= c.input();
  }
}

void ContractorFixpoint::Prune(ContractorStatus* cs) const {
  Box::IntervalVector old_iv{cs->box().interval_vector()};
  do {
    old_iv = cs->box().interval_vector();
    for (const Contractor& ctc : contractors_) {
      ctc.Prune(cs);
      if (cs->box().empty()) {
        return;
      }
    }
  } while (!term_cond_(old_iv, cs->box().interval_vector()));
}

ostream& ContractorFixpoint::display(ostream& os) const {
  os << "Fixpoint(";
  for (const Contractor& c : contractors_) {
    os << c << ", ";
  }
  return os << ")";
}

// ContractorFixpointDep::ContractorFixpointDep(TerminationCondition term_cond,
//                                              vector<Contractor> contractors)
//     : ContractorCell{ibex::BitSet::empty(ComputeInputSize(contractors))},
//       term_cond_{move(term_cond)},
//       contractors_{move(contractors)} {
//   assert(contractors_.size() > 0);
//   ibex::BitSet& input{get_mutable_input()};
//   for (const Contractor& c : contractors_) {
//     input.union_with(c.input());
//   }
// }

// void ContractorFixpointDep::Prune(ContractorStatus* cs) const {
//   static Box::IntervalVector old_iv{cs->box().interval_vector()};
//   do {
//     old_iv = cs->box().interval_vector();
//     for (const Contractor& ctc : contractors_) {
//       ctc.Prune(cs);
//       if (cs->box().empty()) {
//         return;
//       }
//     }
//   } while (!term_cond_(old_iv, cs->box().interval_vector()));
// }

// ostream& ContractorFixpointDep::display(ostream& os) const {
//   os << "FixpointDep(";
//   for (const Contractor& c : contractors_) {
//     os << c << ", ";
//   }
//   return os << ")";
// }

}  // namespace dreal
