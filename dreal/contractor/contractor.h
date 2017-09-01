#pragma once
#include <iostream>
#include <memory>
#include <vector>

#include "./ibex.h"

#include "dreal/contractor/contractor_status.h"
#include "dreal/util/box.h"
#include "dreal/util/ibex_converter.h"

namespace dreal {

// Forward declarations.
class ContractorCell;
class ContractorId;
class ContractorInteger;
class ContractorSeq;
class ContractorIbexFwdbwd;
class ContractorIbexPolytope;
class ContractorFixpoint;
class ContractorJoin;
template <typename ContextType>
class ContractorForall;

// Box::IntervalVector × Box::IntervalVector → Bool
using TerminationCondition =
    std::function<bool(Box::IntervalVector const&, Box::IntervalVector const&)>;

class Contractor {
 public:
  enum class Kind {
    ID,
    INTEGER,
    SEQ,
    IBEX_FWDBWD,
    IBEX_POLYTOPE,
    FIXPOINT,
    FORALL,
    JOIN,
  };

  /// Constructs an idempotent contractor.
  Contractor();

  /// Default copy constructor.
  Contractor(const Contractor&) = default;

  /// Default move constructor.
  Contractor(Contractor&&) = default;

  /// Default copy assign operator.
  Contractor& operator=(const Contractor&) = default;

  /// Default move assign operator.
  Contractor& operator=(Contractor&&) = default;

  /// Default destructor.
  ~Contractor() = default;

  /// Returns the input vector of this contractor. `input()[i] = true`
  /// means that this contractor depends on the value of `box[i]`.
  const ibex::BitSet& input() const;

  /// Prunes @p cs.
  void Prune(ContractorStatus* cs) const;

  /// Returns kind.
  Kind kind() const;

  friend std::ostream& operator<<(std::ostream& os, Contractor const& c);

 private:
  explicit Contractor(const std::shared_ptr<ContractorCell>& ptr);

  std::shared_ptr<ContractorCell> ptr_{};

  friend Contractor make_contractor_id();
  friend Contractor make_contractor_integer(const Box& box);
  friend Contractor make_contractor_seq(
      const std::vector<Contractor>& contractors);
  friend Contractor make_contractor_ibex_fwdbwd(Formula f, const Box& box);
  friend Contractor make_contractor_ibex_polytope(std::vector<Formula> formulas,
                                                  const Box& box);
  friend Contractor make_contractor_fixpoint(
      TerminationCondition term_cond,
      const std::vector<Contractor>& contractors);
  template <typename ContextType>
  friend Contractor make_contractor_forall(Variables quantified_variables,
                                           Formula f, const Box& box,
                                           double delta1, double delta2,
                                           bool use_polytope);
  friend Contractor make_contractor_join(std::vector<Contractor> vec);

  // Note that the following converter functions are only for
  // low-level operations. To use them, you need to include
  // "contractor_cell.h" file.
  friend std::shared_ptr<ContractorId> to_id(const Contractor& contractor);
  friend std::shared_ptr<ContractorInteger> to_integer(
      const Contractor& contractor);
  friend std::shared_ptr<ContractorSeq> to_seq(const Contractor& contractor);
  friend std::shared_ptr<ContractorIbexFwdbwd> to_ibex_fwdbwd(
      const Contractor& contractor);
  friend std::shared_ptr<ContractorIbexPolytope> to_ibex_polytope(
      const Contractor& contractor);
  friend std::shared_ptr<ContractorFixpoint> to_fixpoint(
      const Contractor& contractor);
  friend std::shared_ptr<ContractorJoin> to_join(const Contractor& contractor);
  template <typename ContextType>
  friend std::shared_ptr<ContractorForall<ContextType>> to_forall(
      const Contractor& contractor);
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
Contractor make_contractor_seq(const std::vector<Contractor>& contractors);

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
                                    const std::vector<Contractor>& contractors);

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

/// Returns true if @p contractor is idempotent contractor.
bool is_id(const Contractor& contractor);

/// Returns true if @p contractor is integer contractor.
bool is_integer(const Contractor& contractor);

/// Returns true if @p contractor is sequential contractor.
bool is_seq(const Contractor& contractor);

/// Returns true if @p contractor is IBEX fwdbwd contractor.
bool is_ibex_fwdbwd(const Contractor& contractor);

/// Returns true if @p contractor is IBEX polytope contractor.
bool is_ibex_polytope(const Contractor& contractor);

/// Returns true if @p contractor is fixpoint contractor.
bool is_fixpoint(const Contractor& contractor);

/// Returns true if @p contractor is forall contractor.
bool is_forall(const Contractor& contractor);

/// Returns true if @p contractor is join contractor.
bool is_join(const Contractor& contractor);

}  // namespace dreal
