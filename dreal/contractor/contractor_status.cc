#include "dreal/contractor/contractor_status.h"

#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/logging.h"
#include "dreal/util/stat.h"
#include "dreal/util/timer.h"

using std::move;
using std::set;
using std::vector;

namespace dreal {

namespace {

using std::cout;

// A class to show statistics information at destruction.
class ContractorStatusStat : public Stat {
 public:
  explicit ContractorStatusStat(const bool enabled) : Stat{enabled} {}
  ContractorStatusStat(const ContractorStatusStat&) = default;
  ContractorStatusStat(ContractorStatusStat&&) = default;
  ContractorStatusStat& operator=(const ContractorStatusStat&) = default;
  ContractorStatusStat& operator=(ContractorStatusStat&&) = default;
  ~ContractorStatusStat() override {
    if (enabled()) {
      using fmt::print;
      print(cout, "{:<45} @ {:<20} = {:>15}\n",
            "Total # of Explanation Generations", "ContractorStatus level",
            num_explanation_generation_);
      if (num_explanation_generation_) {
        print(cout, "{:<45} @ {:<20} = {:>15f} sec\n",
              "Total time spent in Explanation Generations",
              "ContractorStatus level",
              timer_explanation_generation_.seconds());
      }
    }
  }

  int num_explanation_generation_{0};
  Timer timer_explanation_generation_;
};

}  // namespace

ContractorStatus::ContractorStatus(Box box, const int branching_point)
    : box_{move(box)},
      branching_point_{branching_point},
      output_{ibex::BitSet::empty(box_.size())} {
  DREAL_ASSERT(!box_.empty());
  DREAL_ASSERT(branching_point_ >= -1 && branching_point_ < box_.size());
}

const Box& ContractorStatus::box() const { return box_; }

Box& ContractorStatus::mutable_box() { return box_; }

int ContractorStatus::branching_point() const { return branching_point_; }

int& ContractorStatus::mutable_branching_point() { return branching_point_; }

const ibex::BitSet& ContractorStatus::output() const { return output_; }

ibex::BitSet& ContractorStatus::mutable_output() { return output_; }

void ContractorStatus::AddUsedConstraint(const Formula& f) {
  DREAL_LOG_DEBUG("ContractorStatus::AddUsedConstraint({}) box is empty? {}", f,
                  box_.empty());
  if (box_.empty()) {
    for (const Variable& v : f.GetFreeVariables()) {
      AddUnsatWitness(v);
    }
  }
  used_constraints_.insert(f);
}

void ContractorStatus::AddUsedConstraint(const vector<Formula>& formulas) {
  for (const Formula& f : formulas) {
    AddUsedConstraint(f);
  }
}

void ContractorStatus::AddUnsatWitness(const Variable& var) {
  DREAL_LOG_DEBUG("ContractorStatus::AddUnsatWitness({})", var);
  unsat_witness_.insert(var);
}

set<Formula> GenerateExplanation(const Variables& unsat_witness,
                                 const set<Formula>& used_constraints) {
  static ContractorStatusStat stat(DREAL_LOG_INFO_ENABLED);
  stat.num_explanation_generation_++;
  TimerGuard timer_guard(&stat.timer_explanation_generation_, stat.enabled());
  if (unsat_witness.empty()) {
    return set<Formula>();
  }

  // Explanation:
  // = lfp. λE. E ∪ {fᵢ | fᵢ ∈ Used Constraints ∧ vars(fᵢ) ∩ unsat_witness ≠ ∅}
  //              ∪ {fᵢ | fᵢ ∈ E ∧
  //                      fⱼ ∈ Used Constraints ∧
  //                      fᵢ and fⱼ share a common variable}.

  // Set up the initial explanation based on variables.
  set<Formula> explanation;
  for (const Formula& f_i : used_constraints) {
    if (HaveIntersection(unsat_witness, f_i.GetFreeVariables())) {
      explanation.insert(f_i);
    }
  }
  bool keep_going = true;
  while (keep_going) {
    keep_going = false;
    for (const Formula& f_i : explanation) {
      const Variables& variables_in_f_i{f_i.GetFreeVariables()};
      for (const Formula& f_j : used_constraints) {
        if (explanation.count(f_j) > 0) {
          continue;
        }
        if (HaveIntersection(variables_in_f_i, f_j.GetFreeVariables())) {
          explanation.insert(f_j);
          keep_going = true;
        }
      }
    }
  }
  return explanation;
}

set<Formula> ContractorStatus::Explanation() const {
  return GenerateExplanation(unsat_witness_, used_constraints_);
}

ContractorStatus& ContractorStatus::InplaceJoin(
    const ContractorStatus& contractor_status) {
  box_.InplaceUnion(contractor_status.box());
  output_ |= contractor_status.output();
  unsat_witness_.insert(contractor_status.unsat_witness_.begin(),
                        contractor_status.unsat_witness_.end());
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
