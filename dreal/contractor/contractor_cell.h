#pragma once

#include <iostream>
#include <memory>
#include <vector>

#include "./ibex.h"

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_status.h"

namespace dreal {

class ContractorCell {
 public:
  // TODO(soonho): revisit this hack.
  ContractorCell() : input_{1} {};
  virtual ~ContractorCell() = default;
  explicit ContractorCell(ibex::BitSet input);
  const ibex::BitSet& input() const;
  ibex::BitSet& get_mutable_input();
  virtual void Prune(ContractorStatus* cs) const = 0;
  virtual std::ostream& display(std::ostream& os) const = 0;

 private:
  ibex::BitSet input_;
};

/// Returns max(c₁.input().max(), ..., cₙ.input().max()).
/// This is used in ContractorSeq and ContractorFixpoint to find the size of its
/// input BitSet.
int ComputeInputSize(const std::vector<Contractor>& contractors);

std::ostream& operator<<(std::ostream& os, const ContractorCell& c);

}  // namespace dreal
