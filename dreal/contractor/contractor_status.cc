#include "dreal/contractor/contractor_status.h"

#include <utility>

#include "dreal/util/assert.h"

using std::move;
using std::unordered_set;
using std::vector;

namespace dreal {

ContractorStatus::ContractorStatus(Box box, const int branching_point)
    : box_{move(box)},
      branching_point_{branching_point},
      output_{ibex::BitSet::empty(box_.size())} {
  DREAL_ASSERT(box_.size() > 0);
  DREAL_ASSERT(branching_point_ >= -1 && branching_point_ < box_.size());
}

const Box& ContractorStatus::box() const { return box_; }

Box& ContractorStatus::mutable_box() { return box_; }

int ContractorStatus::branching_point() const { return branching_point_; }

int& ContractorStatus::mutable_branching_point() { return branching_point_; }

const ibex::BitSet& ContractorStatus::output() const { return output_; }

ibex::BitSet& ContractorStatus::mutable_output() { return output_; }

void ContractorStatus::AddUsedConstraint(const Formula& f) {
  used_constraints_.insert(f);
}

void ContractorStatus::AddUsedConstraint(const vector<Formula>& formulas) {
  used_constraints_.insert(formulas.begin(), formulas.end());
}

const unordered_set<Formula, hash_value<Formula>>&
ContractorStatus::explanation() const {
  return used_constraints_;
}

ContractorStatus& ContractorStatus::InplaceJoin(
    const ContractorStatus& contractor_status) {
  box_.InplaceUnion(contractor_status.box());
  output_ |= contractor_status.output();
  used_constraints_.insert(contractor_status.used_constraints_.begin(),
                           contractor_status.used_constraints_.end());
  return *this;
}

ContractorStatus Join(ContractorStatus contractor_status1,
                      const ContractorStatus& contractor_status2) {
  // This function updates `contractor_status1`, which is passed by value, and
  // returns it.
  return contractor_status1.InplaceJoin(contractor_status2);
}

}  // namespace dreal
