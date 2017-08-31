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

using std::any_of;
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
      const vector<Contractor>& contractors{to_seq(contractor)->contractors()};
      vec.insert(vec.end(), contractors.begin(), contractors.end());
    } else {
      vec.push_back(contractor);
    }
  }
  return vec;
}

}  // namespace

Contractor::Contractor() : ptr_{make_shared<ContractorId>()} {}

Contractor::Contractor(const shared_ptr<ContractorCell>& ptr) : ptr_(ptr) {}

const ibex::BitSet& Contractor::input() const { return ptr_->input(); }

void Contractor::Prune(ContractorStatus* cs) const { ptr_->Prune(cs); }

Contractor::Kind Contractor::kind() const { return ptr_->kind(); }

Contractor make_contractor_id() { return Contractor{}; }

Contractor make_contractor_integer(const Box& box) {
  if (any_of(box.variables().begin(), box.variables().end(),
             [](const Variable& v) {
               return v.get_type() == Variable::Type::INTEGER;
             })) {
    return Contractor{make_shared<ContractorInteger>(box)};
  } else {
    return make_contractor_id();
  }
}

Contractor make_contractor_seq(const vector<Contractor>& contractors) {
  return Contractor{make_shared<ContractorSeq>(Flatten(contractors))};
}

Contractor make_contractor_ibex_fwdbwd(Formula f, const Box& box) {
  return Contractor{make_shared<ContractorIbexFwdbwd>(move(f), box)};
}

Contractor make_contractor_ibex_polytope(vector<Formula> formulas,
                                         const Box& box) {
  return Contractor{make_shared<ContractorIbexPolytope>(move(formulas), box)};
}

Contractor make_contractor_fixpoint(TerminationCondition term_cond,
                                    const vector<Contractor>& contractors) {
  return Contractor{
      make_shared<ContractorFixpoint>(move(term_cond), Flatten(contractors))};
}

Contractor make_contractor_join(vector<Contractor> vec) {
  return Contractor{make_shared<ContractorJoin>(move(vec))};
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
bool is_forall(const Contractor& contractor) {
  return contractor.kind() == Contractor::Kind::FORALL;
}
bool is_join(const Contractor& contractor) {
  return contractor.kind() == Contractor::Kind::JOIN;
}

}  // namespace dreal
