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
#include "dreal/contractor/contractor_fixpoint.h"

#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/exception.h"
#include "dreal/util/interrupt.h"
#include "dreal/util/logging.h"

using std::ostream;
using std::vector;

namespace dreal {

ContractorFixpoint::ContractorFixpoint(TerminationCondition term_cond,
                                       vector<Contractor> contractors,
                                       const Config& config)
    : ContractorCell{Contractor::Kind::FIXPOINT,
                     DynamicBitset(ComputeInputSize(contractors)), config},
      term_cond_{std::move(term_cond)},
      contractors_{std::move(contractors)} {
  DREAL_ASSERT(!contractors_.empty());
  DynamicBitset& input{mutable_input()};
  for (const Contractor& c : contractors_) {
    input |= c.input();
    if (c.include_forall()) {
      set_include_forall();
    }
  }
}

void ContractorFixpoint::Prune(ContractorStatus* cs) const {
  const Box::IntervalVector& iv{cs->box().interval_vector()};
  Box::IntervalVector old_iv{iv};
  do {
    // Note that 'DREAL_CHECK_INTERRUPT' is only defined in setup.py,
    // when we build dReal python package.
#ifdef DREAL_CHECK_INTERRUPT
    if (g_interrupted) {
      DREAL_LOG_DEBUG("KeyboardInterrupt(SIGINT) Detected.");
      throw std::runtime_error("KeyboardInterrupt(SIGINT) Detected.");
    }
#endif
    old_iv = iv;
    for (const Contractor& ctc : contractors_) {
      ctc.Prune(cs);
      if (iv.is_empty()) {
        return;
      }
    }
  } while (!term_cond_(old_iv, iv));
}

ostream& ContractorFixpoint::display(ostream& os) const {
  os << "Fixpoint(";
  for (const Contractor& c : contractors_) {
    os << c << ", ";
  }
  return os << ")";
}

}  // namespace dreal
