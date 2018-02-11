#include "dreal/contractor/contractor_worklist_fixpoint.h"

#include <algorithm>  // To suppress cpplint
#include <cmath>
#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/logging.h"

using std::move;
using std::ostream;
using std::vector;

namespace dreal {

namespace {

void UpdateWorklist(const ibex::BitSet& output,
                    const vector<ibex::BitSet>& input_to_contractors,
                    ibex::BitSet* const worklist) {
  for (int j = 0, changed_dim = output.min(); j < output.size();
       ++j, changed_dim = output.next(changed_dim)) {
    *worklist |= input_to_contractors[changed_dim];
  }
}
}  // namespace

ContractorWorklistFixpoint::ContractorWorklistFixpoint(
    TerminationCondition term_cond, vector<Contractor> contractors,
    const Config& config)
    : ContractorCell{Contractor::Kind::WORKLIST_FIXPOINT,
                     ibex::BitSet::empty(ComputeInputSize(contractors)),
                     config},
      term_cond_{move(term_cond)},
      contractors_{move(contractors)},
      input_to_contractors_{static_cast<size_t>(ComputeInputSize(contractors_)),
                            ibex::BitSet::empty(contractors_.size())},
      worklist_{ibex::BitSet::empty(contractors_.size())},
      old_iv_{1 /* It will be updated anyway. */} {
  DREAL_ASSERT(!contractors_.empty());
  // Setup the input member.
  ibex::BitSet& input{mutable_input()};
  for (const Contractor& ctc : contractors_) {
    input |= ctc.input();
  }

  // Setup input_to_contractors_.
  if (!input.empty()) {
    for (int i = 0; i <= input.max(); ++i) {
      for (size_t j = 0; j < contractors_.size(); ++j) {
        if (contractors_[j].input()[i]) {
          input_to_contractors_[i].add(j);
        }
      }
    }
  }
}

/**
Q : list of contractors
Ctc : list of all contractors

Need to fill Q using "branched dimensions"

If branched_dimension = -1:
    Q.push(Ctc)
else:
    Q.push(ctc ∣ ctc ∈ Ctc ∧ branched_dimension ∈ ctc.input())

while ¬Q.empty() ∧ ¬TermCond(b, b'):
    ctc : contractor ← Q.pop_front();
    b' : box ← ctc.prune(b)
    output : set of integers ← ctc.output()
    for i in output:
        Q.push({ctc ∣ ctc ∈ Ctc ∧ i ∈ ctc.input()})
*/
void ContractorWorklistFixpoint::Prune(ContractorStatus* cs) const {
  worklist_.clear();
  const int branching_point = cs->branching_point();

  // DREAL_LOG_ERROR("ContractorWorklistFixpoint::Prune -- Fill the Queue");
  // 1. Fill the queue.
  old_iv_ = cs->box().interval_vector();
  if (branching_point < 0) {
    // No branching_point information specified, add all contractors.
    for (const auto& contractor : contractors_) {
      // TODO(soonho): Need to save cs->output() and restore after
      // running UpdateWorklist() below. For now, it should be OK
      // since we do not call ContractorWorklistFixpoint::Prune()
      // recursively.
      cs->mutable_output().clear();
      contractor.Prune(cs);
      if (cs->box().empty()) {
        return;
      }
      UpdateWorklist(cs->output(), input_to_contractors_, &worklist_);
    }
  } else {
    const ibex::BitSet& contractors_to_check{
        input_to_contractors_[branching_point]};
    for (int i = 0, ctc_idx = contractors_to_check.min();
         i < contractors_to_check.size();
         ++i, ctc_idx = contractors_to_check.next(ctc_idx)) {
      cs->mutable_output().clear();
      contractors_[ctc_idx].Prune(cs);
      if (cs->box().empty()) {
        return;
      }
      UpdateWorklist(cs->output(), input_to_contractors_, &worklist_);
    }
  }
  if (worklist_.empty() || term_cond_(old_iv_, cs->box().interval_vector())) {
    return;
  }

  // 2. Run worklist algorithm
  do {
    int ctc_idx = worklist_.min();
    old_iv_ = cs->box().interval_vector();
    while (true) {
      worklist_.remove(ctc_idx);
      cs->mutable_output().clear();
      contractors_[ctc_idx].Prune(cs);
      if (cs->box().empty()) {
        return;
      }
      UpdateWorklist(cs->output(), input_to_contractors_, &worklist_);
      if (worklist_.empty()) {
        return;
      }
      if (ctc_idx >= worklist_.max()) {
        break;
      }
      ctc_idx = worklist_.next(ctc_idx);
    }
  } while (!term_cond_(old_iv_, cs->box().interval_vector()));
}

ostream& ContractorWorklistFixpoint::display(ostream& os) const {
  os << "WorklistFixpoint(";
  for (const Contractor& c : contractors_) {
    os << c << ", ";
  }
  return os << ")";
}

}  // namespace dreal
