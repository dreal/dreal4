#include "dreal/contractor/contractor_status.h"

#include <utility>

using std::move;
using std::unordered_set;
using std::vector;

namespace dreal {

ContractorStatus::ContractorStatus(Box box, const int branching_point)
    : box_{move(box)},
      branching_point_{branching_point},
      output_{ibex::BitSet::empty(box_.size())} {
  assert(box_.size() > 0);
  assert(branching_point_ >= -1 && branching_point_ < box_.size());
}

const Box& ContractorStatus::box() const { return box_; }

Box& ContractorStatus::mutable_box() { return box_; }

int ContractorStatus::branching_point() const { return branching_point_; }

int& ContractorStatus::mutable_branching_point() { return branching_point_; }

const ibex::BitSet& ContractorStatus::output() const { return output_; }

ibex::BitSet& ContractorStatus::mutable_output() { return output_; }

void ContractorStatus::AddUsedConstraint(Formula f) {
  if (box_.empty()) {
    unsat_witness_.clear();
    unsat_witness_.push_back(f);
  }
  used_constraints_.emplace(std::move(f));
}

void ContractorStatus::AddUsedConstraint(const vector<Formula>& formulas) {
  if (box_.empty()) {
    unsat_witness_ = formulas;
  }
  used_constraints_.insert(formulas.begin(), formulas.end());
}

unordered_set<Formula, hash_value<Formula>> GenerateExplanation(
    const vector<Formula>& formulas,
    const unordered_set<Formula, hash_value<Formula>>& used_constraints) {
  // Generate an explanation given the fact that the unsat is caused by
  // `formulas`.
  unordered_set<Formula, hash_value<Formula>> explanation{formulas.begin(),
                                                          formulas.end()};
  bool keep_going = true;
  while (keep_going) {
    keep_going = false;
    for (const Formula& f_i : explanation) {
      for (const Formula& f_j : used_constraints) {
        if (explanation.count(f_j) > 0) {
          continue;
        }
        if (!intersect(f_i.GetFreeVariables(), f_j.GetFreeVariables())
                 .empty()) {
          explanation.insert(f_j);
          keep_going = true;
        }
      }
    }
  }
  return explanation;
}

unordered_set<Formula, hash_value<Formula>> ContractorStatus::explanation()
    const {
  return GenerateExplanation(unsat_witness_, used_constraints_);
}

ContractorStatus& ContractorStatus::InplaceJoin(
    const ContractorStatus& contractor_status) {
  box_.InplaceUnion(contractor_status.box());
  output_ |= contractor_status.output();
  used_constraints_.insert(contractor_status.used_constraints_.begin(),
                           contractor_status.used_constraints_.end());
  unsat_witness_.insert(unsat_witness_.end(),
                        contractor_status.unsat_witness_.begin(),
                        contractor_status.unsat_witness_.end());
  return *this;
}

ContractorStatus Join(ContractorStatus contractor_status1,
                      const ContractorStatus& contractor_status2) {
  // This function updates `contractor_status1`, which is passed by value, and
  // returns it.
  return contractor_status1.InplaceJoin(contractor_status2);
}

}  // namespace dreal
