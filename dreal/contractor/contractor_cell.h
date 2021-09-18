/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
#pragma once

#include <iostream>
#include <memory>
#include <vector>

#include "./ibex.h"

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_status.h"
#include "dreal/solver/config.h"

namespace dreal {

// Forward declarations.
class ContractorCell;
class ContractorId;
class ContractorInteger;
class ContractorSeq;
class ContractorIbexFwdbwd;
class ContractorIbexPolytope;
class ContractorFixpoint;
class ContractorWorklistFixpoint;
class ContractorJoin;
template <typename ContextType>
class ContractorForall;

/// Abstract base class of contractors.
class ContractorCell {
 public:
  /// Constructs a cell with @p kind and @p input.
  ContractorCell(Contractor::Kind kind, DynamicBitset input, Config config);

  /// Deleted default constructor.
  ContractorCell() = delete;

  /// Deleted copy constructor.
  ContractorCell(const ContractorCell&) = delete;

  /// Deleted move constructor.
  ContractorCell(ContractorCell&&) = delete;

  /// Deleted copy assign operator.
  void operator=(const ContractorCell&) = delete;

  /// Deleted move assign operator.
  void operator=(ContractorCell&&) = delete;

  /// Default destructor.
  virtual ~ContractorCell() = default;

  /// Returns its kind.
  Contractor::Kind kind() const;

  /// Returns its input.
  const DynamicBitset& input() const;

  /// Returns its input.
  DynamicBitset& mutable_input();

  /// Returns config.
  const Config& config() const;

  /// Returns true if this contractor includes a forall contractor.
  bool include_forall() const;

  /// Sets include_forall true.
  void set_include_forall();

  /// Performs pruning on @p cs.
  virtual void Prune(ContractorStatus* cs) const = 0;

  /// Outputs this contractor to @p os.
  virtual std::ostream& display(std::ostream& os) const = 0;

 private:
  const Contractor::Kind kind_;
  DynamicBitset input_;
  const Config config_;
  bool include_forall_{false};
};

// Returns max(c₁.input().size(), ..., cₙ.input().size()).
// This is used in ContractorSeq, ContractorFixpoint, and
// ContractorWorklistFixpoint to find the size of its input DynamicBitset.
DynamicBitset::size_type ComputeInputSize(
    const std::vector<Contractor>& contractors);

std::ostream& operator<<(std::ostream& os, const ContractorCell& c);

/// Converts @p contractor to ContractorId.
std::shared_ptr<ContractorId> to_id(const Contractor& contractor);

/// Converts @p contractor to ContractorInteger.
std::shared_ptr<ContractorInteger> to_integer(const Contractor& contractor);

/// Converts @p contractor to ContractorSeq.
std::shared_ptr<ContractorSeq> to_seq(const Contractor& contractor);

/// Converts @p contractor to ContractorIbexFwdbwd.
std::shared_ptr<ContractorIbexFwdbwd> to_ibex_fwdbwd(
    const Contractor& contractor);

/// Converts @p contractor to ContractorIbexPolytop.
std::shared_ptr<ContractorIbexPolytope> to_ibex_polytope(
    const Contractor& contractor);

/// Converts @p contractor to ContractorFixpoint.
std::shared_ptr<ContractorFixpoint> to_fixpoint(const Contractor& contractor);

/// Converts @p contractor to ContractorWorklistFixpoint.
std::shared_ptr<ContractorWorklistFixpoint> to_worklist_fixpoint(
    const Contractor& contractor);

/// Converts @p contractor to ContractorJoin.
std::shared_ptr<ContractorJoin> to_join(const Contractor& contractor);

/// Converts @p contractor to ContractorForall.
template <typename ContextType>
std::shared_ptr<ContractorForall<ContextType>> to_forall(
    const Contractor& contractor);

}  // namespace dreal
