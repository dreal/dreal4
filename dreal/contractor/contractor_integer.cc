#include "dreal/contractor/contractor_integer.h"

#include <cmath>

#include "dreal/util/assert.h"
#include "dreal/util/math.h"

using std::ostream;

namespace dreal {

ContractorInteger::ContractorInteger(const Box& box, const Config& config)
    : ContractorCell{Contractor::Kind::INTEGER, ibex::BitSet::empty(box.size()),
                     config} {
  ibex::BitSet& input{mutable_input()};
  for (int i = 0; i < box.size(); ++i) {
    const Variable::Type type{box.variable(i).get_type()};
    if (type == Variable::Type::INTEGER || type == Variable::Type::BINARY) {
      int_indexes_.push_back(i);
      input.add(i);
    }
  }
  DREAL_ASSERT(!int_indexes_.empty());
}

void ContractorInteger::Prune(ContractorStatus* contractor_status) const {
  Box& box{contractor_status->mutable_box()};
  for (const int idx : int_indexes_) {
    Box::Interval& iv{box[idx]};
    if (iv.is_degenerated()) {
      continue;
    }
    if (!is_integer(iv.lb()) || !is_integer(iv.ub())) {
      const double new_lb{std::ceil(iv.lb())};
      const double new_ub{std::floor(iv.ub())};
      if (new_lb <= new_ub) {
        iv = Box::Interval{new_lb, new_ub};
        contractor_status->mutable_output().add(idx);
      } else {
        // [new_lb, new_ub] = empty
        box.set_empty();
        contractor_status->AddUnsatWitness(box.variable(idx));
        contractor_status->mutable_output().fill(
            0, contractor_status->box().size() - 1);
        return;
      }
    }
  }
}

ostream& ContractorInteger::display(ostream& os) const {
  return os << "Integer()";
}

}  // namespace dreal
