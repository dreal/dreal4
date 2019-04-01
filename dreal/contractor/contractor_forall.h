#pragma once

#include <cmath>
#include <memory>
#include <ostream>
#include <stdexcept>
#include <utility>

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_cell.h"
#include "dreal/contractor/counterexample_refiner.h"
#include "dreal/contractor/generic_contractor_generator.h"
#include "dreal/util/assert.h"
#include "dreal/util/box.h"
#include "dreal/util/logging.h"
#include "dreal/util/nnfizer.h"
#include "dreal/util/optional.h"

namespace dreal {

/// Add Doc.
Box RefineCounterexample(const Formula& query,
                         const Variables& quantified_variables, Box b,
                         double precision);

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
/// We do this by computing Solve(strengthen(¬φ, ε), δ) where ε > δ.
///
///  - Case 1: No CE found.
///            This means that any point in B satisfies the quantified
///            portion of F.
///
///  - Case 2: Found a CE, (a₁, ..., aₙ, b₁, ..., bₘ).
///            Use the CE to reduce B into B'. That is compute,
///
///            B' = Contract(φ(x₁, ..., xₙ, b₁, ..., bₘ), B)
///
/// </pre>
template <typename ContextType>
class ContractorForall : public ContractorCell {
 public:
  /// Constructs Forall contractor using @p f and @p box. @p epsilon is
  /// used to strengthen ¬φ and @p inner_delta is used to solve (¬φ)⁻ᵟ¹.
  ///
  /// @pre 0.0 < inner_delta < epsilon < config.precision().
  ContractorForall(Formula f, const Box& box, double epsilon,
                   double inner_delta, const Config& config)
      : ContractorCell{Contractor::Kind::FORALL,
                       ibex::BitSet::empty(box.size()), config},
        f_{std::move(f)},
        quantified_variables_{get_quantified_variables(f_)},
        strengthend_negated_nested_f_{Nnfizer{}.Convert(
            DeltaStrengthen(!get_quantified_formula(f_), epsilon), true)},
        contractor_{config /* This one will be updated anyway. */},
        context_for_counterexample_{config} {
    DREAL_ASSERT(epsilon > 0.0);
    DREAL_ASSERT(inner_delta > 0.0);
    DREAL_ASSERT(config.precision() > epsilon);
    DREAL_ASSERT(epsilon > inner_delta);
    DREAL_ASSERT(!is_false(strengthend_negated_nested_f_));

    // Setup context:
    // 0. Setup context, config, and the contractor for finding counterexamples.
    context_for_counterexample_.mutable_config().mutable_precision() =
        inner_delta;
    context_for_counterexample_.mutable_config().mutable_use_polytope() =
        config.use_polytope_in_forall();
    contractor_ = GenericContractorGenerator{}.Generate(
        get_quantified_formula(f_), ExtendBox(box, quantified_variables_),
        context_for_counterexample_.config());
    // 1. Add exist/forall variables.
    for (const Variable& exist_var : box.variables()) {
      context_for_counterexample_.DeclareVariable(exist_var);
    }
    for (const Variable& forall_var : get_quantified_variables(f_)) {
      context_for_counterexample_.DeclareVariable(forall_var);
    }
    // 2. Assert strengthen(¬φ, ε).
    if (is_conjunction(strengthend_negated_nested_f_)) {
      // Optimizations
      for (const Formula& formula :
           get_operands(strengthend_negated_nested_f_)) {
        context_for_counterexample_.Assert(formula);
      }
    } else {
      context_for_counterexample_.Assert(strengthend_negated_nested_f_);
    }

    // Build input.
    ibex::BitSet& input{mutable_input()};
    for (const Variable& v : f_.GetFreeVariables()) {
      input.add(box.index(v));
    }
    if (this->config().use_local_optimization()) {
      refiner_ = std::make_unique<CounterexampleRefiner>(
          strengthend_negated_nested_f_, quantified_variables_,
          context_for_counterexample_.config());
    }
  }

  /// Deleted copy constructor.
  ContractorForall(const ContractorForall&) = delete;

  /// Deleted move constructor.
  ContractorForall(ContractorForall&&) = delete;

  /// Deleted copy assign operator.
  ContractorForall& operator=(const ContractorForall&) = delete;

  /// Deleted move assign operator.
  ContractorForall& operator=(ContractorForall&&) = delete;

  bool PruneWithCounterexample(ContractorStatus* cs, Box* const current_box,
                               const Box& counterexample) const {
    // Need to prune the current_box using counterexample.
    ContractorStatus contractor_status(counterexample);
    // 1.1.1. Set up exist_var parts for pruning
    for (const Variable& exist_var : current_box->variables()) {
      contractor_status.mutable_box()[exist_var] = (*current_box)[exist_var];
    }
    // 1.1.2. Set up universal_var parts from
    // counterexample. Narrow down the forall variables part by
    // taking the mid-points of counterexample.
    for (const Variable& forall_var : get_quantified_variables(f_)) {
      contractor_status.mutable_box()[forall_var] =
          counterexample[forall_var].mid();
    }
    contractor_.Prune(&contractor_status);
    if (contractor_status.box().empty()) {
      // If the pruning result is empty, there is nothing more to do. Exit
      // the loop.
      cs->mutable_output().fill(0, cs->box().size() - 1);
      current_box->set_empty();
      return true;
    } else {
      // Otherwise, we update the current box and keep looping.
      bool changed = false;
      for (int i = 0; i < cs->box().size(); ++i) {
        if (cs->box()[i] != contractor_status.box()[i]) {
          cs->mutable_output().add(i);
          (*current_box)[i] = contractor_status.box()[i];
          changed = true;
        }
      }
      if (!changed) {
        // We reached at a fixed-point.
        return true;
      }
    }
    return false;
  }

  /// Default destructor.
  ~ContractorForall() override = default;

  void Prune(ContractorStatus* cs) const override {
    Box& current_box = cs->mutable_box();
    Config& config_for_counterexample{
        context_for_counterexample_.mutable_config()};
    while (true) {
      // 1. Find Counterexample.
      for (const Variable& exist_var : current_box.variables()) {
        context_for_counterexample_.SetInterval(exist_var,
                                                current_box[exist_var].lb(),
                                                current_box[exist_var].ub());
      }
      // Alternate the stacking order.
      config_for_counterexample.mutable_stack_left_box_first() =
          !config_for_counterexample.stack_left_box_first();
      optional<Box> counterexample_opt = context_for_counterexample_.CheckSat();
      if (counterexample_opt) {
        Box& counterexample{*counterexample_opt};
        // 1.1. Counterexample found.
        DREAL_LOG_DEBUG("ContractorForall::Prune: Counterexample found:\n{}",
                        counterexample);

        if (config().use_local_optimization()) {
          counterexample = refiner_->Refine(counterexample);
        }
        bool need_to_break_the_loop =
            PruneWithCounterexample(cs, &current_box, counterexample);
        if (need_to_break_the_loop) {
          break;
        }
      } else {
        // 1.2. No counterexample found.
        DREAL_LOG_DEBUG("ContractorForall::Prune: No counterexample found.");
        break;
      }
    }
    cs->AddUsedConstraint(f_);
  }

  std::ostream& display(std::ostream& os) const override { return os << f_; }

 private:
  static Box ExtendBox(Box box, const Variables& vars) {
    for (const Variable& v : vars) {
      box.Add(v);
    }
    return box;
  }

  const Formula f_;                             // ∀X.φ
  const Variables quantified_variables_;        // X
  const Formula strengthend_negated_nested_f_;  // (¬φ)⁻ᵟ¹
  // To compute `B' = Contract(φ(x₁, ..., xₙ, b₁, ..., bₘ), B)`.
  Contractor contractor_;
  // Context to do `Solve(¬φ', δ₂)`.
  mutable ContextType context_for_counterexample_;
  const bool use_local_optimization_{false};

  std::unique_ptr<CounterexampleRefiner> refiner_;
};

template <typename ContextType>
Contractor make_contractor_forall(Formula f, const Box& box, double epsilon,
                                  double inner_delta, const Config& config) {
  return Contractor{std::make_shared<ContractorForall<ContextType>>(
      std::move(f), box, epsilon, inner_delta, config)};
}

/// Converts @p contractor to ContractorForall.
template <typename ContextType>
std::shared_ptr<ContractorForall<ContextType>> to_forall(
    const Contractor& contractor) {
  DREAL_ASSERT(is_forall(contractor));
  return std::static_pointer_cast<ContractorForall<ContextType>>(
      contractor.ptr_);
}

}  // namespace dreal
