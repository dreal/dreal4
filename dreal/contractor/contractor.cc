#include "dreal/contractor/contractor.h"

#include <algorithm>
#include <utility>

#include "dreal/contractor/contractor_cell.h"
#include "dreal/contractor/contractor_fixpoint.h"
#include "dreal/contractor/contractor_forall.h"
#include "dreal/contractor/contractor_ibex_fwdbwd.h"
#include "dreal/contractor/contractor_ibex_polytope.h"
#include "dreal/contractor/contractor_id.h"
#include "dreal/contractor/contractor_integer.h"
#include "dreal/contractor/contractor_join.h"
#include "dreal/contractor/contractor_seq.h"
#include "dreal/contractor/contractor_worklist_fixpoint.h"
#include "dreal/util/stat.h"

using std::any_of;
using std::cout;
using std::make_shared;
using std::move;
using std::ostream;
using std::shared_ptr;
using std::vector;

namespace dreal {

namespace {

// Flattens contractors and filters out ID contractors.
vector<Contractor> Flatten(const vector<Contractor>& contractors) {
  vector<Contractor> vec;
  vec.reserve(contractors.size());
  for (const Contractor& contractor : contractors) {
    const Contractor::Kind kind{contractor.kind()};
    if (kind == Contractor::Kind::ID) {
      // Skip if contractor == ID.
      continue;
    } else if (kind == Contractor::Kind::SEQ) {
      // Flatten it out if contractor == SEQ.
      const vector<Contractor>& contractors_inside{
          to_seq(contractor)->contractors()};
      vec.insert(vec.end(), contractors_inside.begin(),
                 contractors_inside.end());
    } else {
      vec.push_back(contractor);
    }
  }
  return vec;
}

// A class to show statistics information at destruction. We have a
// static instance in Contractor::Prune() to keep track of the number
// of pruning operations.
class ContractorStat : public Stat {
 public:
  explicit ContractorStat(const bool enabled) : Stat{enabled} {}
  ContractorStat(const ContractorStat&) = default;
  ContractorStat(ContractorStat&&) = default;
  ContractorStat& operator=(const ContractorStat&) = default;
  ContractorStat& operator=(ContractorStat&&) = default;
  ~ContractorStat() override {
    if (enabled()) {
      using fmt::print;
      print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of Pruning",
            "Contractor level", num_prune_);
    }
  }
  int num_prune_{0};
};

}  // namespace

Contractor::Contractor(const Config& config)
    : ptr_{make_shared<ContractorId>(config)} {}

Contractor::Contractor(std::shared_ptr<ContractorCell> ptr) : ptr_{move(ptr)} {}

const ibex::BitSet& Contractor::input() const { return ptr_->input(); }

void Contractor::Prune(ContractorStatus* cs) const {
  static ContractorStat stat{DREAL_LOG_INFO_ENABLED};
  stat.num_prune_++;
  ptr_->Prune(cs);
}

Contractor::Kind Contractor::kind() const { return ptr_->kind(); }

Contractor make_contractor_id(const Config& config) {
  return Contractor{config};
}

Contractor make_contractor_integer(const Box& box, const Config& config) {
  if (any_of(box.variables().begin(), box.variables().end(),
             [](const Variable& v) {
               const Variable::Type type{v.get_type()};
               return type == Variable::Type::INTEGER ||
                      type == Variable::Type::BINARY;
             })) {
    return Contractor{make_shared<ContractorInteger>(box, config)};
  } else {
    return make_contractor_id(config);
  }
}

Contractor make_contractor_seq(const vector<Contractor>& contractors,
                               const Config& config) {
  return Contractor{make_shared<ContractorSeq>(Flatten(contractors), config)};
}

Contractor make_contractor_ibex_fwdbwd(Formula f, const Box& box,
                                       const Config& config) {
  return Contractor{make_shared<ContractorIbexFwdbwd>(move(f), box, config)};
}

Contractor make_contractor_ibex_polytope(vector<Formula> formulas,
                                         const Box& box, const Config& config) {
  return Contractor{
      make_shared<ContractorIbexPolytope>(move(formulas), box, config)};
}

Contractor make_contractor_fixpoint(TerminationCondition term_cond,
                                    const vector<Contractor>& contractors,
                                    const Config& config) {
  vector<Contractor> ctcs{Flatten(contractors)};
  if (ctcs.empty()) {
    return make_contractor_id(config);
  } else {
    return Contractor{
        make_shared<ContractorFixpoint>(move(term_cond), move(ctcs), config)};
  }
}

Contractor make_contractor_worklist_fixpoint(
    TerminationCondition term_cond, const vector<Contractor>& contractors,
    const Config& config) {
  vector<Contractor> ctcs{Flatten(contractors)};
  if (ctcs.empty()) {
    return make_contractor_id(config);
  } else {
    return Contractor{make_shared<ContractorWorklistFixpoint>(
        move(term_cond), move(ctcs), config)};
  }
}

Contractor make_contractor_join(vector<Contractor> vec, const Config& config) {
  return Contractor{make_shared<ContractorJoin>(move(vec), config)};
}

ostream& operator<<(ostream& os, const Contractor& ctc) {
  if (ctc.ptr_) {
    os << *(ctc.ptr_);
  }
  return os;
}

bool is_id(const Contractor& contractor) {
  return contractor.kind() == Contractor::Kind::ID;
}
bool is_integer(const Contractor& contractor) {
  return contractor.kind() == Contractor::Kind::INTEGER;
}
bool is_seq(const Contractor& contractor) {
  return contractor.kind() == Contractor::Kind::SEQ;
}
bool is_ibex_fwdbwd(const Contractor& contractor) {
  return contractor.kind() == Contractor::Kind::IBEX_FWDBWD;
}
bool is_ibex_polytope(const Contractor& contractor) {
  return contractor.kind() == Contractor::Kind::IBEX_POLYTOPE;
}
bool is_fixpoint(const Contractor& contractor) {
  return contractor.kind() == Contractor::Kind::FIXPOINT;
}
bool is_worklist_fixpoint(const Contractor& contractor) {
  return contractor.kind() == Contractor::Kind::WORKLIST_FIXPOINT;
}
bool is_forall(const Contractor& contractor) {
  return contractor.kind() == Contractor::Kind::FORALL;
}
bool is_join(const Contractor& contractor) {
  return contractor.kind() == Contractor::Kind::JOIN;
}

}  // namespace dreal
