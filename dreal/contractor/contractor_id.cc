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
#include "dreal/contractor/contractor_id.h"

using std::ostream;

namespace dreal {
ContractorId::ContractorId(const Config& config)
    : ContractorCell{Contractor::Kind::ID,
                     DynamicBitset(1) /* this is meaningless */, config} {}

void ContractorId::Prune(ContractorStatus*) const {
  // No op.
}
ostream& ContractorId::display(ostream& os) const { return os << "ID()"; }

}  // namespace dreal
