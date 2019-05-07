#include "dreal/solver/icp_stat.h"

#include <ostream>

#include <fmt/format.h>
#include <fmt/ostream.h>

using std::cout;

namespace dreal {

IcpStat::~IcpStat() {
  if (enabled()) {
    using fmt::print;
    print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of Branching",
          "ICP level", num_branch_);
    print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of Pruning", "ICP level",
          num_prune_);
    if (num_branch_) {
      print(cout, "{:<45} @ {:<20} = {:>15f} sec\n",
            "Total time spent in Branching", "ICP level",
            timer_branch_.seconds());
    }
    if (num_prune_) {
      print(cout, "{:<45} @ {:<20} = {:>15f} sec\n",
            "Total time spent in Pruning", "ICP level", timer_prune_.seconds());
    }
    print(cout, "{:<45} @ {:<20} = {:>15f} sec\n",
          "Total time spent in Evaluation", "ICP level", timer_eval_.seconds());
  }
}
}  // namespace dreal
