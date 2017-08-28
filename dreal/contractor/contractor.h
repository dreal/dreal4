#pragma once

#include <iostream>
#include <memory>
#include <vector>

#include "./ibex.h"

#include "dreal/contractor/contractor_status.h"
#include "dreal/util/box.h"
#include "dreal/util/ibex_converter.h"

namespace dreal {

class ContractorCell;  // Forward declaration.

// Box::IntervalVector × Box::IntervalVector → Bool
using TerminationCondition =
    std::function<bool(Box::IntervalVector const&, Box::IntervalVector const&)>;

class Contractor {
 public:
  /// Constructs an idempotent contractor.
  Contractor();

  /// Returns the input vector of this contractor. `input()[i] = true`
  /// means that this contractor depends on the value of `box[i]`.
  const ibex::BitSet& input() const;

  /// Prunes @p cs.
  void Prune(ContractorStatus* cs) const;
  friend std::ostream& operator<<(std::ostream& os, Contractor const& c);

 private:
  explicit Contractor(const std::shared_ptr<ContractorCell>& ptr);

  std::shared_ptr<ContractorCell> ptr_{};

  friend Contractor make_contractor_id();
  friend Contractor make_contractor_integer(const Box& box);
  friend Contractor make_contractor_seq(std::vector<Contractor> vec);
  friend Contractor make_contractor_ibex_fwdbwd(Formula f, const Box& box);
  friend Contractor make_contractor_ibex_polytope(std::vector<Formula> formulas,
                                                  const Box& box);
  friend Contractor make_contractor_fixpoint(TerminationCondition term_cond,
                                             std::vector<Contractor> vec);
  template <typename ContextType>
  friend Contractor make_contractor_forall(Variables quantified_variables,
                                           Formula f, const Box& box,
                                           double delta1, double delta2,
                                           bool use_polytope);
  friend Contractor make_contractor_join(std::vector<Contractor> vec);
};

/// Returns an idempotent contractor.
/// @see ContractorId.
Contractor make_contractor_id();

/// Returns an integer contractor. For an integer variable `v`, it
/// prunes `b[v] = [lb, ub]` into `[ceil(lb), floor(ub)]`. It sets the box empty
/// if it detects an empty interval in pruning.
///
/// @see ContractorInteger.
Contractor make_contractor_integer(const Box& box);

/// Returns a sequential contractor `C` from a vector of contractors
/// @p vec = [C₁, ..., Cₙ]. It applies `Cᵢ` sequentially. That is, we have:
/// <pre>
///     C(box) = (Cₙ∘...∘C₁)(box)
/// </pre>
///
/// @see ContractorSeq.
Contractor make_contractor_seq(std::vector<Contractor> vec);

/// Returns a contractor wrapping IBEX's forward/backward contractor.
///
/// @see ContractorIbexFwdbwd.
Contractor make_contractor_ibex_fwdbwd(Formula f, const Box& box);

/// Returns a contractor wrapping IBEX's polytope contractor.
///
/// @see ContractorIbexPolytope.
Contractor make_contractor_ibex_polytope(std::vector<Formula> formulas,
                                         const Box& box);

/// Returns a fixed-point contractor. The returned contractor applies
/// the contractors in @p vec sequentially until @p term_cond is met.
///
/// @see ContractorFixpoint.
Contractor make_contractor_fixpoint(TerminationCondition term_cond,
                                    std::vector<Contractor> vec);

/// Returns a join contractor. The returned contractor does the following
/// operation:
/// <pre>
///     (C₁ ∨ ... ∨ Cₙ)(box) = C₁(box) ∨ ... ∨ Cₙ(box).
/// </pre>
///
/// @see ContractorJoin.
Contractor make_contractor_join(std::vector<Contractor> vec);

/// Returns a forall contractor.
///
/// @note the implementation is at `dreal/contractor/contractor_forall.h` file.
/// @see ContractorForall.
template <typename ContextType>
Contractor make_contractor_forall(Variables quantified_variables, Formula f,
                                  const Box& box, double delta1, double delta2,
                                  bool use_polytope);

std::ostream& operator<<(std::ostream& os, const Contractor& ctc);

}  // namespace dreal
