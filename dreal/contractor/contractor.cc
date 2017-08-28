#include "dreal/contractor/contractor.h"

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

using std::make_shared;
using std::move;
using std::ostream;
using std::shared_ptr;
using std::vector;

namespace dreal {

Contractor::Contractor() : ptr_{make_shared<ContractorId>()} {}

Contractor::Contractor(const shared_ptr<ContractorCell>& ptr) : ptr_(ptr) {}

const ibex::BitSet& Contractor::input() const { return ptr_->input(); }

void Contractor::Prune(ContractorStatus* cs) const { ptr_->Prune(cs); }

Contractor make_contractor_id() { return Contractor{}; }

Contractor make_contractor_integer(const Box& box) {
  return Contractor{make_shared<ContractorInteger>(box)};
}

Contractor make_contractor_seq(vector<Contractor> vec) {
  return Contractor{make_shared<ContractorSeq>(move(vec))};
}

Contractor make_contractor_ibex_fwdbwd(Formula f, const Box& box) {
  return Contractor{make_shared<ContractorIbexFwdbwd>(move(f), box)};
}

Contractor make_contractor_ibex_polytope(std::vector<Formula> formulas,
                                         const Box& box) {
  return Contractor{make_shared<ContractorIbexPolytope>(move(formulas), box)};
}

Contractor make_contractor_fixpoint(TerminationCondition term_cond,
                                    vector<Contractor> vec) {
  return Contractor{
      make_shared<ContractorFixpoint>(move(term_cond), move(vec))};
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

}  // namespace dreal
