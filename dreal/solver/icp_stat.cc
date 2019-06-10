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
    if (num_branch_) {
      print(cout, "{:<45} @ {:<16} T{:<2} = {:>15f} sec\n",
            "Total time spent in Branching", "ICP level", thread_id_,
            timer_branch_.seconds());
    }
    if (num_prune_) {
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
