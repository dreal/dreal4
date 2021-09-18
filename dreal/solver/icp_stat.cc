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
#include "dreal/solver/icp_stat.h"

#include <ostream>

#include <fmt/format.h>
#include <fmt/ostream.h>

using std::cout;

namespace dreal {

IcpStat::~IcpStat() {
  if (enabled()) {
    using fmt::print;
    print(cout, "{:<45} @ {:<16} T{:<2} = {:>15}\n", "Total # of Branching",
          "ICP level", thread_id_, num_branch_);
    print(cout, "{:<45} @ {:<16} T{:<2} = {:>15}\n", "Total # of Pruning",
          "ICP level", thread_id_, num_prune_);
    if (num_branch_ > 0) {
      print(cout, "{:<45} @ {:<16} T{:<2} = {:>15f} sec\n",
            "Total time spent in Branching", "ICP level", thread_id_,
            timer_branch_.seconds());
    }
    if (num_prune_ > 0) {
      print(cout, "{:<45} @ {:<16} T{:<2} = {:>15f} sec\n",
            "Total time spent in Pruning", "ICP level", thread_id_,
            timer_prune_.seconds());
    }
    print(cout, "{:<45} @ {:<16} T{:<2} = {:>15f} sec\n",
          "Total time spent in Evaluation", "ICP level", thread_id_,
          timer_eval_.seconds());
  }
}
}  // namespace dreal
