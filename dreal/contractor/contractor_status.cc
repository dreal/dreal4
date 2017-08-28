#include "dreal/contractor/contractor_status.h"

#include <utility>

using std::move;
using std::set;
using std::vector;

namespace dreal {

ContractorStatus::ContractorStatus(Box box)
    : box_{move(box)}, output_{ibex::BitSet::empty(box_.size())} {}

const Box& ContractorStatus::box() const { return box_; }

Box& ContractorStatus::get_mutable_box() { return box_; }

const ibex::BitSet& ContractorStatus::output() const { return output_; }

ibex::BitSet& ContractorStatus::get_mutable_output() { return output_; }

void ContractorStatus::AddUsedConstraint(Formula f) {
  used_constraints_.emplace(std::move(f));
}

void ContractorStatus::AddUsedConstraint(const vector<Formula>& formulas) {
  used_constraints_.insert(formulas.begin(), formulas.end());
}

const set<Formula>& ContractorStatus::used_constraints() const {
  return used_constraints_;
}

set<Formula>& ContractorStatus::get_mutable_used_constraints() {
  return used_constraints_;
}

ContractorStatus& ContractorStatus::InplaceJoin(
    const ContractorStatus& contractor_status) {
  box_.InplaceUnion(contractor_status.box());
  output_ |= contractor_status.output();
  used_constraints_.insert(contractor_status.used_constraints().begin(),
                           contractor_status.used_constraints().end());
  return *this;
}

ContractorStatus Join(ContractorStatus contractor_status1,
                      const ContractorStatus& contractor_status2) {
  // This function updates `contractor_status1`, which is passed by value, and
  // returns it.
  return contractor_status1.InplaceJoin(contractor_status2);
}

}  // namespace dreal
