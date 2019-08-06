#include "dreal/util/if_then_else_eliminator.h"

#include <algorithm>  // To suppress cpplint on max.
#include <atomic>
#include <set>
#include <stdexcept>
#include <string>

#include "dreal/util/logging.h"
#include "dreal/util/nnfizer.h"
#include "dreal/util/stat.h"
#include "dreal/util/timer.h"

using std::cout;
using std::set;
using std::to_string;
using std::unordered_set;

namespace dreal {

// A class to show statistics information at destruction.
class IfThenElseElimStat : public Stat {
 public:
  explicit IfThenElseElimStat(const bool enabled) : Stat{enabled} {}
  IfThenElseElimStat(const IfThenElseElimStat&) = delete;
  IfThenElseElimStat(IfThenElseElimStat&&) = delete;
  IfThenElseElimStat& operator=(const IfThenElseElimStat&) = delete;
  IfThenElseElimStat& operator=(IfThenElseElimStat&&) = delete;
  ~IfThenElseElimStat() override {
    if (enabled()) {
      using fmt::print;
      print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of Process",
            "ITE Elim", num_process_);
      if (num_process_ > 0) {
        print(cout, "{:<45} @ {:<20} = {:>15f} sec\n",
              "Total time spent in Processing", "ITE Elim",
              timer_process_.seconds());
      }
    }
  }

  void increase_num_process() { increase(&num_process_); }

  Timer timer_process_;

 private:
  std::atomic<int> num_process_{0};
};

Formula IfThenElseEliminator::Process(const Formula& f) {
  static IfThenElseElimStat stat{DREAL_LOG_INFO_ENABLED};
  TimerGuard timer_guard(&stat.timer_process_, stat.enabled());
  stat.increase_num_process();

  Formula new_f{Visit(f, Formula::True())};
  if (f.EqualTo(new_f) && added_formulas_.empty()) {
    return f;
  } else {
    return new_f && make_conjunction(added_formulas_);
  }
}

const unordered_set<Variable, hash_value<Variable>>&
IfThenElseEliminator::variables() const {
  return ite_variables_;
}

Expression IfThenElseEliminator::Visit(const Expression& e,
                                       const Formula& guard) {
  return VisitExpression<Expression>(this, e, guard);
}

Expression IfThenElseEliminator::VisitVariable(const Expression& e,
                                               const Formula&) {
  return e;
}

Expression IfThenElseEliminator::VisitConstant(const Expression& e,
                                               const Formula&) {
  return e;
}

Expression IfThenElseEliminator::VisitRealConstant(const Expression& e,
                                                   const Formula&) {
  return e;
}

Expression IfThenElseEliminator::VisitAddition(const Expression& e,
                                               const Formula& guard) {
  // e = c₀ + ∑ᵢ cᵢ * eᵢ
  Expression ret{get_constant_in_addition(e)};
  for (const auto& p : get_expr_to_coeff_map_in_addition(e)) {
    const Expression& e_i{p.first};
    const double c_i{p.second};
    ret += c_i * Visit(e_i, guard);
  }
  return ret;
}

Expression IfThenElseEliminator::VisitMultiplication(const Expression& e,
                                                     const Formula& guard) {
  // e = c₀ * ∏ᵢ pow(eᵢ₁, eᵢ₂)
  Expression ret{get_constant_in_multiplication(e)};
  for (const auto& p : get_base_to_exponent_map_in_multiplication(e)) {
    const Expression& e_i1{p.first};
    const Expression& e_i2{p.second};
    ret *= pow(Visit(e_i1, guard), Visit(e_i2, guard));
  }
  return ret;
}

Expression IfThenElseEliminator::VisitDivision(const Expression& e,
                                               const Formula& guard) {
  return Visit(get_first_argument(e), guard) /
         Visit(get_second_argument(e), guard);
}

Expression IfThenElseEliminator::VisitLog(const Expression& e,
                                          const Formula& guard) {
  return log(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAbs(const Expression& e,
                                          const Formula& guard) {
  return abs(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitExp(const Expression& e,
                                          const Formula& guard) {
  return exp(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitSqrt(const Expression& e,
                                           const Formula& guard) {
  return sqrt(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitPow(const Expression& e,
                                          const Formula& guard) {
  return pow(Visit(get_first_argument(e), guard),
             Visit(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitSin(const Expression& e,
                                          const Formula& guard) {
  return sin(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitCos(const Expression& e,
                                          const Formula& guard) {
  return cos(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitTan(const Expression& e,
                                          const Formula& guard) {
  return tan(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAsin(const Expression& e,
                                           const Formula& guard) {
  return asin(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAcos(const Expression& e,
                                           const Formula& guard) {
  return acos(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAtan(const Expression& e,
                                           const Formula& guard) {
  return atan(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitAtan2(const Expression& e,
                                            const Formula& guard) {
  return atan2(Visit(get_first_argument(e), guard),
               Visit(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitSinh(const Expression& e,
                                           const Formula& guard) {
  return sinh(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitCosh(const Expression& e,
                                           const Formula& guard) {
  return cosh(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitTanh(const Expression& e,
                                           const Formula& guard) {
  return tanh(Visit(get_argument(e), guard));
}

Expression IfThenElseEliminator::VisitMin(const Expression& e,
                                          const Formula& guard) {
  return min(Visit(get_first_argument(e), guard),
             Visit(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitMax(const Expression& e,
                                          const Formula& guard) {
  return max(Visit(get_first_argument(e), guard),
             Visit(get_second_argument(e), guard));
}

Expression IfThenElseEliminator::VisitIfThenElse(const Expression& e,
                                                 const Formula& guard) {
  static int counter{0};
  const Variable new_var{"ITE" + to_string(counter++),
                         Variable::Type::CONTINUOUS};
  ite_variables_.insert(new_var);
  const Formula c{Visit(get_conditional_formula(e), guard)};
  const Formula then_guard{guard && c};
  const Formula else_guard{guard && !c};
  const Expression e1{Visit(get_then_expression(e), then_guard)};
  const Expression e2{Visit(get_else_expression(e), else_guard)};
  // (then_guard ∧ (new_var = e1)) ∨ (else_guard ∧ (new_var = e2))
  added_formulas_.push_back((then_guard && (new_var == e1)) ||
                            (else_guard && (new_var == e2)));
  return new_var;
}

Expression IfThenElseEliminator::VisitUninterpretedFunction(const Expression& e,
                                                            const Formula&) {
  return e;
}

Formula IfThenElseEliminator::Visit(const Formula& f, const Formula& guard) {
  return VisitFormula<Formula>(this, f, guard);
}

Formula IfThenElseEliminator::VisitFalse(const Formula& f, const Formula&) {
  return f;
}

Formula IfThenElseEliminator::VisitTrue(const Formula& f, const Formula&) {
  return f;
}

Formula IfThenElseEliminator::VisitVariable(const Formula& f, const Formula&) {
  return f;
}

Formula IfThenElseEliminator::VisitEqualTo(const Formula& f,
                                           const Formula& guard) {
  return Visit(get_lhs_expression(f), guard) ==
         Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitNotEqualTo(const Formula& f,
                                              const Formula& guard) {
  return Visit(get_lhs_expression(f), guard) !=
         Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitGreaterThan(const Formula& f,
                                               const Formula& guard) {
  return Visit(get_lhs_expression(f), guard) >
         Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitGreaterThanOrEqualTo(const Formula& f,
                                                        const Formula& guard) {
  return Visit(get_lhs_expression(f), guard) >=
         Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitLessThan(const Formula& f,
                                            const Formula& guard) {
  return Visit(get_lhs_expression(f), guard) <
         Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitLessThanOrEqualTo(const Formula& f,
                                                     const Formula& guard) {
  return Visit(get_lhs_expression(f), guard) <=
         Visit(get_rhs_expression(f), guard);
}

Formula IfThenElseEliminator::VisitConjunction(const Formula& f,
                                               const Formula& guard) {
  // f := f₁ ∧ ... ∧ fₙ
  set<Formula> new_conjuncts;
  for (const Formula& f_i : get_operands(f)) {
    new_conjuncts.emplace(Visit(f_i, guard));
  }
  return make_conjunction(new_conjuncts);
}

Formula IfThenElseEliminator::VisitDisjunction(const Formula& f,
                                               const Formula& guard) {
  // f := f₁ ∨ ... ∨ fₙ
  set<Formula> new_disjuncts;
  for (const Formula& f_i : get_operands(f)) {
    new_disjuncts.emplace(Visit(f_i, guard));
  }
  return make_disjunction(new_disjuncts);
}

Formula IfThenElseEliminator::VisitNegation(const Formula& f,
                                            const Formula& guard) {
  return !Visit(get_operand(f), guard);
}

Formula IfThenElseEliminator::VisitForall(const Formula& f, const Formula&) {
  //    ∃x. ∀y. ITE(f, e₁, e₂) > 0
  // => ∃x. ¬∃y. ¬(ITE(f, e₁, e₂) > 0)
  // => ∃x. ¬∃y. ∃v. ¬(v > 0) ∧ (f → (v = e₁)) ∧ (¬f → (v = e₂))
  // => ∃x. ∀y. ∀v. ¬(¬(v > 0) ∧ (f → (v = e₁)) ∧ (¬f → (v = e₂)))
  // => ∃x. ∀y. ∀v. (v > 0) ∨ ¬((f → (v = e₁)) ∧ (¬f → (v = e₂)))
  // => ∃x. ∀y. ∀v. ¬((f → (v = e₁)) ∧ (¬f → (v = e₂))) ∨ (v > 0)
  // => ∃x. ∀y. ∀v. ((f → (v = e₁)) ∧ (¬f → (v = e₂))) → (v > 0)
  // => ∃x. ∀y. ∀v. (v > 0) ∨ (f ∧ (v ≠ e₁)) ∨ (¬f ∧ (v ≠ e₂)).

  // Note that we have the following:
  // => ∃x. ∀y. ∀v. ¬(¬(v > 0) ∧ ¬(f ∧ (v ≠ e₁)) ∧ ¬(¬f ∧ (v ≠ e₂)).
  // => ∃x. ∀y. ∀v. ¬(¬(v > 0) ∧ (¬f ∨ (v = e₁)) ∧ (f ∨ (v = e₂)).
  // => ∃x. ∀y. ∀v. ¬(¬(v > 0) ∧ (f → (v = e₁)) ∧ (¬f → (v = e₂)).
  //
  // That is, we can first process the negation of the original
  // formula `ITE(f, e₁, e₂) > 0`, then negate the result again while
  // collecting the newly introduced variables (`v`s) to treat them as
  // universally quantified variables (instead of existential
  // variables). In this way, we can use the existing ITE-elim routine.
  Variables quantified_variables{get_quantified_variables(f)};
  const Formula& quantified_formula{get_quantified_formula(f)};
  IfThenElseEliminator ite_eliminator_forall;
  const Formula eliminated{ite_eliminator_forall.Process(!quantified_formula)};
  quantified_variables.insert(ite_eliminator_forall.variables().begin(),
                              ite_eliminator_forall.variables().end());
  return forall(quantified_variables, Nnfizer{}.Convert(!eliminated));
}

}  // namespace dreal
