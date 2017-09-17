#pragma once

#include <cmath>
#include <memory>
#include <ostream>
#include <stdexcept>
#include <utility>
#include <experimental/optional>

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_cell.h"
#include "dreal/contractor/generic_contractor_generator.h"
#include "dreal/util/box.h"
#include "dreal/util/logging.h"
#include "dreal/util/nnfizer.h"

namespace dreal {
/// Contractor for forall constraints. See the following problem
/// definition and our approach.
///
/// <pre>
/// Problem: Given a box B ∈ IRⁿ and a formula F =
/// ∃x₁...xₙ. ∀y₁....yₘ. φ(x₁, ..., xₙ, y₁, ..., yₘ), design a
/// contractor reducing B into B' where B' ⊆ B.
///
/// Approach: Find a counterexample (a₁, ..., aₙ, b₁, ..., bₘ) such
/// that ¬φ(a₁, ..., aₙ, b₁, ..., bₘ) holds while (a₁, ..., aₙ) ∈ B.
/// We do this by computing Solve((¬φ)⁻ᵟ¹, δ₂) where δ₁ > δ₂.
///
///  - Case 1: No CE found.
///            This means that any point in B satisfies the quantified
///            portion of F.
///
///  - Case 2: Found a CE, (a₁, ..., aₙ, b₁, ..., bₘ).
///            Use the CE to reduce B into B'. That is compute,
///
///            B' = Contract(φ(x₁, ..., xₙ, b₁, ..., bₘ), B)
/// </pre>
template <typename ContextType>
class ContractorForall : public ContractorCell {
 public:
  /// Constructs Forall contractor using @p f and @p box. @p delta1 is
  /// used to strengthen ¬φ and @p delta2 is used to solve (¬φ)⁻ᵟ¹.
  ///
  /// @pre delta1 > delta2 > 0.0
  ContractorForall(Variables quantified_variables, Formula f, const Box& box,
                   double delta1, double delta2, bool use_polytope)
      : ContractorCell{Contractor::Kind::FORALL,
                       ibex::BitSet::empty(box.size())},
        quantified_variables_{std::move(quantified_variables)},
        f_{std::move(f)},
        strengthend_neg_f_{
            Nnfizer{}.Convert(DeltaStrengthen(!f_, delta1), use_polytope)},
        contractor_{GenericContractorGenerator{}.Generate(
            f_, ExtendBox(box, quantified_variables_), use_polytope)} {
    assert(delta1 > 0.0);
    assert(delta2 > 0.0);
    assert(delta1 > delta2);

    // Setup context:
    // 1. Add exist/forall variables.
    context_for_counterexample_.get_mutable_config().set_precision(delta2);
    for (const Variable& exist_var : box.variables()) {
      context_for_counterexample_.DeclareVariable(exist_var);
    }
    for (const Variable& forall_var : quantified_variables_) {
      context_for_counterexample_.DeclareVariable(forall_var);
    }
    // 2. Assert (¬φ)⁻ᵟ¹.
    if (is_conjunction(strengthend_neg_f_)) {
      // Optimizations
      for (const Formula& f : get_operands(strengthend_neg_f_)) {
        context_for_counterexample_.Assert(f);
      }
    } else {
      context_for_counterexample_.Assert(strengthend_neg_f_);
    }

    // Build input.
    ibex::BitSet& input{mutable_input()};
    for (const Variable& v : f_.GetFreeVariables()) {
      // Add v if v ∈ (vars(f) - quantified_variables).
      if (quantified_variables_.include(v)) {
        input.add(box.index(v));
      }
    }
  }

  /// Default destructor.
  ~ContractorForall() override = default;

  void Prune(ContractorStatus* cs) const override {
    Box& current_box = cs->mutable_box();
    while (true) {
      // 1. Find Counterexample.
      for (const Variable& exist_var : current_box.variables()) {
        context_for_counterexample_.SetInterval(exist_var,
                                                current_box[exist_var].lb(),
                                                current_box[exist_var].ub());
      }
      const std::experimental::optional<Box> counterexample =
          context_for_counterexample_.CheckSat();
      if (counterexample) {
        // 1.1. Counterexample found.
        DREAL_LOG_DEBUG("ContractorForall::Prune: Counterexample found:\n{}",
                        *counterexample);
        // Need to prune the current_box using counterexample.
        ContractorStatus contractor_status(*counterexample);
        // 1.1.1. Set up exist_var parts for pruning
        for (const Variable& exist_var : current_box.variables()) {
          contractor_status.mutable_box()[exist_var] = current_box[exist_var];
        }
        // 1.1.2. Set up universal_var parts from
        // counterexample. Narrow down the forall variables part by
        // taking the mid-points of counterexample.
        for (const Variable& forall_var : quantified_variables_) {
          contractor_status.mutable_box()[forall_var] =
              (*counterexample)[forall_var].mid();
        }
        contractor_.Prune(&contractor_status);
        if (contractor_status.box().empty()) {
          // If the pruning result is empty, there is nothing more to do. Exit
          // the loop.
          cs->mutable_output().fill(0, cs->box().size() - 1);
          current_box.set_empty();
          break;
        } else {
          // Otherwise, we update the current box and keep looping.
          bool changed = false;
          for (int i = 0; i < cs->box().size(); ++i) {
            if (cs->box()[i] != contractor_status.box()[i]) {
              cs->mutable_output().add(i);
              current_box[i] = contractor_status.box()[i];
              changed = true;
            }
          }
          if (!changed) {
            // We reached at a fixed-point.
            break;
          }
        }
      } else {
        // 1.2. No counterexample found.
        DREAL_LOG_DEBUG("ContractorForall::Prune: No counterexample found.");
        break;
      }
    }
    cs->AddUsedConstraint(forall(quantified_variables_, f_));
  }

  std::ostream& display(std::ostream& os) const override {
    return os << "Forall(" << quantified_variables_ << ", " << f_ << ")";
  }

 private:
  static Box ExtendBox(Box box, const Variables& vars) {
    for (const Variable& v : vars) {
      box.Add(v);
    }
    return box;
  }

  const Variables quantified_variables_;
  const Formula f_;                  // quantified formula φ.
  const Formula strengthend_neg_f_;  // (¬φ)⁻ᵟ¹.
  // To compute `B' = Contract(φ(x₁, ..., xₙ, b₁, ..., bₘ), B)`.
  Contractor contractor_;
  // Context to do `Solve(¬φ', δ₂)`.
  mutable ContextType context_for_counterexample_;
};

template <typename ContextType>
Contractor make_contractor_forall(Variables quantified_variables, Formula f,
                                  const Box& box, double delta1, double delta2,
                                  bool use_polytope) {
  return Contractor{std::make_shared<ContractorForall<ContextType>>(
      std::move(quantified_variables), std::move(f), box, delta1, delta2,
      use_polytope)};
}

/// Converts @p contractor to ContractorForall.
template <typename ContextType>
std::shared_ptr<ContractorForall<ContextType>> to_forall(
    const Contractor& contractor) {
  assert(is_forall(contractor));
  return std::static_pointer_cast<ContractorForall<ContextType>>(
      contractor.ptr_);
}

}  // namespace dreal
