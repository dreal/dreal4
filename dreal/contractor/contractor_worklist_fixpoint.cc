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
#include "dreal/contractor/contractor_worklist_fixpoint.h"

#include <algorithm>  // To suppress cpplint
#include <cmath>
#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/logging.h"

using std::ostream;
using std::vector;

namespace dreal {

namespace {

void UpdateWorklist(const DynamicBitset& output,
                    const vector<DynamicBitset>& input_to_contractors,
                    DynamicBitset* const worklist) {
  DynamicBitset::size_type i_bit = output.find_first();
  while (i_bit != DynamicBitset::npos) {
    *worklist |= input_to_contractors[i_bit];
    i_bit = output.find_next(i_bit);
  }
}
}  // namespace

ContractorWorklistFixpoint::ContractorWorklistFixpoint(
    TerminationCondition term_cond, vector<Contractor> contractors,
    const Config& config)
    : ContractorCell{Contractor::Kind::WORKLIST_FIXPOINT,
                     DynamicBitset(ComputeInputSize(contractors)), config},
      term_cond_{std::move(term_cond)},
      contractors_{std::move(contractors)},
      input_to_contractors_{static_cast<size_t>(ComputeInputSize(contractors_)),
                            DynamicBitset(contractors_.size())} {
  DREAL_ASSERT(!contractors_.empty());
  // Setup the input member.
  DynamicBitset& input{mutable_input()};
  for (const Contractor& ctc : contractors_) {
    input |= ctc.input();
    if (ctc.include_forall()) {
      set_include_forall();
    }
  }

  // Setup input_to_contractors_.
  for (size_t j = 0; j < contractors_.size(); ++j) {
    for (size_t i = 0; i < contractors_[j].input().size(); ++i) {
      if (contractors_[j].input()[i]) {
        input_to_contractors_[i].set(j);
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
  // worklist[i] means that i-th contractor in contractors_ needs to be
  // applied.
  DynamicBitset worklist(contractors_.size());
  const int branching_point = cs->branching_point();

  // DREAL_LOG_ERROR("ContractorWorklistFixpoint::Prune -- Fill the Queue");
  // 1. Fill the queue.
  const Box::IntervalVector& iv{cs->box().interval_vector()};
  Box::IntervalVector old_iv{iv};
  if (branching_point < 0) {
    // No branching_point information specified, add all contractors.
    for (const auto& contractor : contractors_) {
      // TODO(soonho): Need to save cs->output() and restore after
      // running UpdateWorklist() below. For now, it should be OK
      // since we do not call ContractorWorklistFixpoint::Prune()
      // recursively.
      cs->mutable_output().reset();
      contractor.Prune(cs);
      if (cs->box().empty()) {
        return;
      }
      UpdateWorklist(cs->output(), input_to_contractors_, &worklist);
    }
  } else {
    DREAL_ASSERT(static_cast<size_t>(branching_point) <
                 input_to_contractors_.size());
    const DynamicBitset& contractors_to_check{
        input_to_contractors_[branching_point]};

    DynamicBitset::size_type i_bit = contractors_to_check.find_first();
    while (i_bit != DynamicBitset::npos) {
      cs->mutable_output().reset();
      contractors_[i_bit].Prune(cs);
      if (cs->box().empty()) {
        return;
      }
      UpdateWorklist(cs->output(), input_to_contractors_, &worklist);
      i_bit = contractors_to_check.find_next(i_bit);
    }
  }
  if (worklist.none() || term_cond_(old_iv, iv)) {
    return;
  }

  // 2. Run worklist algorithm
  do {
    DynamicBitset::size_type ctc_idx = worklist.find_first();
    old_iv = iv;
    while (true) {
      worklist.set(ctc_idx, false);
      cs->mutable_output().reset();
      contractors_[ctc_idx].Prune(cs);
      if (cs->box().empty()) {
        return;
      }
      UpdateWorklist(cs->output(), input_to_contractors_, &worklist);
      if (worklist.none()) {
        return;
      }
      ctc_idx = worklist.find_next(ctc_idx);
      if (ctc_idx == DynamicBitset::npos) {
        ctc_idx = worklist.find_first();
      }
    }
  } while (!term_cond_(old_iv, iv));
}

ostream& ContractorWorklistFixpoint::display(ostream& os) const {
  os << "WorklistFixpoint(";
  for (const Contractor& c : contractors_) {
    os << c << ", ";
  }
  return os << ")";
}

}  // namespace dreal
