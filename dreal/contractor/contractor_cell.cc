#include "dreal/contractor/contractor_cell.h"

#include <utility>

using std::move;
using std::ostream;
using std::vector;

namespace dreal {

ContractorCell::ContractorCell(ibex::BitSet input) : input_{move(input)} {}

const ibex::BitSet& ContractorCell::input() const { return input_; }

ibex::BitSet& ContractorCell::get_mutable_input() { return input_; }

// Returns max(c₁.input().max(), ..., cₙ.input().max()).
// This is used in ContractorSeq and ContractorFixpoint to find the size of its
// input BitSet.
int ComputeInputSize(const vector<Contractor>& contractors) {
  int ret = 0;
  for (const Contractor& c : contractors) {
    // When c.input().empty(), c.input().max() has INT_MAX so we need to skip
    // it.
    if (!c.input().empty()) {
      const int max_i = c.input().max();
      if (max_i > ret) {
        ret = max_i;
      }
    }
  }
  return ret + 1;
}

ostream& operator<<(ostream& os, const ContractorCell& c) {
  return c.display(os);
}

}  // namespace dreal
