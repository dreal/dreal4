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
  ContractorCell(Contractor::Kind kind, const ibex::BitSet& input,
                 const Config& config);

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
  const ibex::BitSet& input() const;

  /// Returns its input.
  ibex::BitSet& mutable_input();

  /// Returns config.
  const Config& config() const;

  /// Performs pruning on @p cs.
  virtual void Prune(ContractorStatus* cs) const = 0;

  /// Outputs this contractor to @p os.
  virtual std::ostream& display(std::ostream& os) const = 0;

 private:
  const Contractor::Kind kind_;
  ibex::BitSet input_;
  const Config& config_;
};

/// Returns max(c₁.input().max(), ..., cₙ.input().max()).
///
/// This is used in ContractorSeq, ContractorFixpoint, and
/// ContractorWorklistFixpoint to find the size of its input BitSet.
int ComputeInputSize(const std::vector<Contractor>& contractors);

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
