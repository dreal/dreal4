#include "dreal/contractor/generic_contractor_generator.h"

#include <utility>
#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/util/exception.h"
#include "dreal/util/logging.h"
#include "dreal/util/nnfizer.h"

namespace dreal {

using std::move;
using std::vector;

Contractor GenericContractorGenerator::Generate(const Formula& f,
                                                const Box& box,
                                                const Config& config) const {
  DREAL_LOG_DEBUG("GenericContractorGenerator::Generate({})\n{}", f, box);
  return Visit(Nnfizer{}.Convert(f, true), box, config);
}

Contractor GenericContractorGenerator::Visit(const Formula& f, const Box& box,
                                             const Config& config) const {
  return VisitFormula<Contractor>(this, f, box, config);
}

Contractor GenericContractorGenerator::VisitFalse(const Formula&, const Box&,
                                                  const Config&) const {
  throw DREAL_RUNTIME_ERROR("GenericContractorGenerator: 'False' is detected.");
}

Contractor GenericContractorGenerator::VisitTrue(const Formula&, const Box&,
                                                 const Config& config) const {
  return make_contractor_id(config);
}

Contractor GenericContractorGenerator::VisitVariable(const Formula&, const Box&,
                                                     const Config&) const {
  throw DREAL_RUNTIME_ERROR(
      "GenericContractorGenerator: Boolean variable is detected.");
}

Contractor GenericContractorGenerator::VisitEqualTo(
    const Formula& f, const Box& box, const Config& config) const {
  if (config.use_polytope()) {
    return make_contractor_ibex_polytope({f}, box, config);
  } else {
    return make_contractor_ibex_fwdbwd(f, box, config);
  }
}

Contractor GenericContractorGenerator::VisitNotEqualTo(
    const Formula& f, const Box& box, const Config& config) const {
  if (config.use_polytope()) {
    return make_contractor_ibex_polytope({f}, box, config);
  } else {
    return make_contractor_ibex_fwdbwd(f, box, config);
  }
}

Contractor GenericContractorGenerator::VisitGreaterThan(
    const Formula& f, const Box& box, const Config& config) const {
  if (config.use_polytope()) {
    return make_contractor_ibex_polytope({f}, box, config);
  } else {
    return make_contractor_ibex_fwdbwd(f, box, config);
  }
}

Contractor GenericContractorGenerator::VisitGreaterThanOrEqualTo(
    const Formula& f, const Box& box, const Config& config) const {
  if (config.use_polytope()) {
    return make_contractor_ibex_polytope({f}, box, config);
  } else {
    return make_contractor_ibex_fwdbwd(f, box, config);
  }
}

Contractor GenericContractorGenerator::VisitLessThan(
    const Formula& f, const Box& box, const Config& config) const {
  if (config.use_polytope()) {
    return make_contractor_ibex_polytope({f}, box, config);
  } else {
    return make_contractor_ibex_fwdbwd(f, box, config);
  }
}

Contractor GenericContractorGenerator::VisitLessThanOrEqualTo(
    const Formula& f, const Box& box, const Config& config) const {
  if (config.use_polytope()) {
    return make_contractor_ibex_polytope({f}, box, config);
  } else {
    return make_contractor_ibex_fwdbwd(f, box, config);
  }
}

Contractor GenericContractorGenerator::VisitConjunction(
    const Formula& f, const Box& box, const Config& config) const {
  vector<Contractor> contractors;
  vector<Formula> relational_formulas;
  contractors.reserve(get_operands(f).size());
  for (const Formula& f_i : get_operands(f)) {
    if (config.use_polytope() && is_relational(f_i)) {
      relational_formulas.push_back(f_i);
    } else {
      contractors.push_back(Visit(f_i, box, config));
    }
  }
  if (config.use_polytope()) {
    contractors.push_back(
        make_contractor_ibex_polytope(relational_formulas, box, config));
  }
  return make_contractor_seq(contractors, config);
}

Contractor GenericContractorGenerator::VisitDisjunction(
    const Formula& f, const Box& box, const Config& config) const {
  vector<Contractor> contractors;
  contractors.reserve(get_operands(f).size());
  for (const Formula& f_i : get_operands(f)) {
    contractors.push_back(Visit(f_i, box, config));
  }
  return make_contractor_join(move(contractors), config);
}

Contractor GenericContractorGenerator::VisitNegation(const Formula& f,
                                                     const Box&,
                                                     const Config&) const {
  DREAL_LOG_DEBUG("GenericContractorGenerator::{}", f);
  throw DREAL_RUNTIME_ERROR(
      "GenericContractorGenerator: Negation is detected.");
}

Contractor GenericContractorGenerator::VisitForall(const Formula&, const Box&,
                                                   const Config&) const {
  throw DREAL_RUNTIME_ERROR("GenericContractorGenerator: Forall is detected.");
}

}  // namespace dreal
