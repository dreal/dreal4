#include "dreal/contractor/generic_contractor_generator.h"

#include <stdexcept>
#include <utility>
#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/util/logging.h"
#include "dreal/util/nnfizer.h"

namespace dreal {

using std::move;
using std::runtime_error;
using std::vector;

Contractor GenericContractorGenerator::Generate(const Formula& f,
                                                const Box& box,
                                                const bool use_polytope) const {
  DREAL_LOG_DEBUG("GenericContractorGenerator::Generate({})\n{}", f, box);
  return Visit(Nnfizer{}.Convert(f, true), box, use_polytope);
}

Contractor GenericContractorGenerator::Visit(const Formula& f, const Box& box,
                                             const bool use_polytope) const {
  return VisitFormula<Contractor>(this, f, box, use_polytope);
}

Contractor GenericContractorGenerator::VisitFalse(const Formula&, const Box&,
                                                  const bool) const {
  throw runtime_error{"GenericContractorGenerator: 'False' is detected."};
}

Contractor GenericContractorGenerator::VisitTrue(const Formula&, const Box&,
                                                 const bool) const {
  return make_contractor_id();
}

Contractor GenericContractorGenerator::VisitVariable(const Formula&, const Box&,
                                                     const bool) const {
  throw runtime_error{
      "GenericContractorGenerator: Boolean variable is detected."};
}

Contractor GenericContractorGenerator::VisitEqualTo(
    const Formula& f, const Box& box, const bool use_polytope) const {
  if (use_polytope) {
    return make_contractor_ibex_polytope({f}, box);
  } else {
    return make_contractor_ibex_fwdbwd(f, box);
  }
}

Contractor GenericContractorGenerator::VisitNotEqualTo(
    const Formula& f, const Box& box, const bool use_polytope) const {
  if (use_polytope) {
    return make_contractor_ibex_polytope({f}, box);
  } else {
    return make_contractor_ibex_fwdbwd(f, box);
  }
}

Contractor GenericContractorGenerator::VisitGreaterThan(
    const Formula& f, const Box& box, const bool use_polytope) const {
  if (use_polytope) {
    return make_contractor_ibex_polytope({f}, box);
  } else {
    return make_contractor_ibex_fwdbwd(f, box);
  }
}

Contractor GenericContractorGenerator::VisitGreaterThanOrEqualTo(
    const Formula& f, const Box& box, const bool use_polytope) const {
  if (use_polytope) {
    return make_contractor_ibex_polytope({f}, box);
  } else {
    return make_contractor_ibex_fwdbwd(f, box);
  }
}

Contractor GenericContractorGenerator::VisitLessThan(
    const Formula& f, const Box& box, const bool use_polytope) const {
  if (use_polytope) {
    return make_contractor_ibex_polytope({f}, box);
  } else {
    return make_contractor_ibex_fwdbwd(f, box);
  }
}

Contractor GenericContractorGenerator::VisitLessThanOrEqualTo(
    const Formula& f, const Box& box, const bool use_polytope) const {
  if (use_polytope) {
    return make_contractor_ibex_polytope({f}, box);
  } else {
    return make_contractor_ibex_fwdbwd(f, box);
  }
}

Contractor GenericContractorGenerator::VisitConjunction(
    const Formula& f, const Box& box, const bool use_polytope) const {
  vector<Contractor> contractors;
  vector<Formula> relational_formulas;
  contractors.reserve(get_operands(f).size());
  for (const Formula& f_i : get_operands(f)) {
    if (use_polytope && is_relational(f_i)) {
      relational_formulas.push_back(f_i);
    } else {
      contractors.push_back(Visit(f_i, box, use_polytope));
    }
  }
  if (use_polytope) {
    contractors.push_back(
        make_contractor_ibex_polytope(relational_formulas, box));
  }
  return make_contractor_seq(move(contractors));
}

Contractor GenericContractorGenerator::VisitDisjunction(
    const Formula& f, const Box& box, const bool use_polytope) const {
  vector<Contractor> contractors;
  contractors.reserve(get_operands(f).size());
  for (const Formula& f_i : get_operands(f)) {
    contractors.push_back(Visit(f_i, box, use_polytope));
  }
  return make_contractor_join(move(contractors));
}

Contractor GenericContractorGenerator::VisitNegation(const Formula& f,
                                                     const Box&,
                                                     const bool) const {
  DREAL_LOG_DEBUG("GenericContractorGenerator::{}", f);
  throw runtime_error{"GenericContractorGenerator: Negation is detected."};
}

Contractor GenericContractorGenerator::VisitForall(const Formula&, const Box&,
                                                   const bool) const {
  throw runtime_error{"GenericContractorGenerator: Forall is detected."};
}

}  // namespace dreal
