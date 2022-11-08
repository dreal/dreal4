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
#include "dreal/contractor/contractor_sampling.h"

#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/exception.h"
#include "dreal/util/interrupt.h"
#include "dreal/util/logging.h"

using std::ostream;
using std::vector;

namespace dreal {

ContractorSampling::ContractorSampling(const vector<Formula> input_formulas,
                                       const Box& box, const Config& config)
    : ContractorCell{Contractor::Kind::SAMPLING, DynamicBitset(), config} {
  (void)input_formulas;
  (void)box;
  (void)config;
}

void ContractorSampling::Prune(ContractorStatus* cs) const { (void)cs; }

ostream& ContractorSampling::display(ostream& os) const {
  os << "Sampling";
  return os << ")";
}

}  // namespace dreal
