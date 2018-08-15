#include "dreal/util/if_then_else_eliminator.h"

#include <algorithm>  // To suppress cpplint on max.
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
  IfThenElseElimStat(const IfThenElseElimStat&) = default;
  IfThenElseElimStat(IfThenElseElimStat&&) = default;
  IfThenElseElimStat& operator=(const IfThenElseElimStat&) = default;
  IfThenElseElimStat& operator=(IfThenElseElimStat&&) = default;
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

  int num_process_{0};
  Timer timer_process_;
};

Formula IfThenElseEliminator::Process(const Formula& f) {
  static IfThenElseElimStat stat{DREAL_LOG_INFO_ENABLED};
  TimerGuard timer_guard(&stat.timer_process_, stat.enabled());
  ++stat.num_process_;

  Formula new_f{Visit(f)};
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

Expression IfThenElseEliminator::Visit(const Expression& e) {
  return VisitExpression<Expression>(this, e);
}

Expression IfThenElseEliminator::VisitVariable(const Expression& e) {
  return e;
}

Expression IfThenElseEliminator::VisitConstant(const Expression& e) {
  return e;
}

Expression IfThenElseEliminator::VisitRealConstant(const Expression& e) {
  return e;
}

Expression IfThenElseEliminator::VisitAddition(const Expression& e) {
  // e = c₀ + ∑ᵢ cᵢ * eᵢ
  Expression ret{get_constant_in_addition(e)};
  for (const auto& p : get_expr_to_coeff_map_in_addition(e)) {
    const Expression& e_i{p.first};
    const double c_i{p.second};
    ret += c_i * Visit(e_i);
  }
  return ret;
}

Expression IfThenElseEliminator::VisitMultiplication(const Expression& e) {
  // e = c₀ * ∏ᵢ pow(eᵢ₁, eᵢ₂)
  Expression ret{get_constant_in_multiplication(e)};
  for (const auto& p : get_base_to_exponent_map_in_multiplication(e)) {
    const Expression& e_i1{p.first};
    const Expression& e_i2{p.second};
    ret *= pow(Visit(e_i1), Visit(e_i2));
  }
  return ret;
}

Expression IfThenElseEliminator::VisitDivision(const Expression& e) {
  return Visit(get_first_argument(e)) / Visit(get_second_argument(e));
}

Expression IfThenElseEliminator::VisitLog(const Expression& e) {
  return log(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitAbs(const Expression& e) {
  return abs(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitExp(const Expression& e) {
  return exp(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitSqrt(const Expression& e) {
  return sqrt(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitPow(const Expression& e) {
  return pow(Visit(get_first_argument(e)), Visit(get_second_argument(e)));
}

Expression IfThenElseEliminator::VisitSin(const Expression& e) {
  return sin(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitCos(const Expression& e) {
  return cos(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitTan(const Expression& e) {
  return tan(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitAsin(const Expression& e) {
  return asin(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitAcos(const Expression& e) {
  return acos(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitAtan(const Expression& e) {
  return atan(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitAtan2(const Expression& e) {
  return atan2(Visit(get_first_argument(e)), Visit(get_second_argument(e)));
}

Expression IfThenElseEliminator::VisitSinh(const Expression& e) {
  return sinh(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitCosh(const Expression& e) {
  return cosh(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitTanh(const Expression& e) {
  return tanh(Visit(get_argument(e)));
}

Expression IfThenElseEliminator::VisitMin(const Expression& e) {
  return min(Visit(get_first_argument(e)), Visit(get_second_argument(e)));
}

Expression IfThenElseEliminator::VisitMax(const Expression& e) {
  return max(Visit(get_first_argument(e)), Visit(get_second_argument(e)));
}

Expression IfThenElseEliminator::VisitIfThenElse(const Expression& e) {
  static int counter{0};
  const Variable new_var{"ITE" + to_string(counter++),
                         Variable::Type::CONTINUOUS};
  ite_variables_.insert(new_var);
  const Formula c{Visit(get_conditional_formula(e))};
  const Expression e1{Visit(get_then_expression(e))};
  const Expression e2{Visit(get_else_expression(e))};
  // c ⇒ (new_var = e1)
  added_formulas_.push_back(!c || (new_var == e1));
  // ¬c ⇒ (new_var = e2)
  added_formulas_.push_back(c || (new_var == e2));
  return new_var;
}

Expression IfThenElseEliminator::VisitUninterpretedFunction(
    const Expression& e) {
  return e;
}

Formula IfThenElseEliminator::Visit(const Formula& f) {
  return VisitFormula<Formula>(this, f);
}

Formula IfThenElseEliminator::VisitFalse(const Formula& f) { return f; }

Formula IfThenElseEliminator::VisitTrue(const Formula& f) { return f; }

Formula IfThenElseEliminator::VisitVariable(const Formula& f) { return f; }

Formula IfThenElseEliminator::VisitEqualTo(const Formula& f) {
  return Visit(get_lhs_expression(f)) == Visit(get_rhs_expression(f));
}

Formula IfThenElseEliminator::VisitNotEqualTo(const Formula& f) {
  return Visit(get_lhs_expression(f)) != Visit(get_rhs_expression(f));
}

Formula IfThenElseEliminator::VisitGreaterThan(const Formula& f) {
  return Visit(get_lhs_expression(f)) > Visit(get_rhs_expression(f));
}

Formula IfThenElseEliminator::VisitGreaterThanOrEqualTo(const Formula& f) {
  return Visit(get_lhs_expression(f)) >= Visit(get_rhs_expression(f));
}

Formula IfThenElseEliminator::VisitLessThan(const Formula& f) {
  return Visit(get_lhs_expression(f)) < Visit(get_rhs_expression(f));
}

Formula IfThenElseEliminator::VisitLessThanOrEqualTo(const Formula& f) {
  return Visit(get_lhs_expression(f)) <= Visit(get_rhs_expression(f));
}

Formula IfThenElseEliminator::VisitConjunction(const Formula& f) {
  // f := f₁ ∧ ... ∧ fₙ
  set<Formula> new_conjuncts;
  for (const Formula& f_i : get_operands(f)) {
    new_conjuncts.emplace(Visit(f_i));
  }
  return make_conjunction(new_conjuncts);
}

Formula IfThenElseEliminator::VisitDisjunction(const Formula& f) {
  // f := f₁ ∨ ... ∨ fₙ
  set<Formula> new_disjuncts;
  for (const Formula& f_i : get_operands(f)) {
    new_disjuncts.emplace(Visit(f_i));
  }
  return make_disjunction(new_disjuncts);
}

Formula IfThenElseEliminator::VisitNegation(const Formula& f) {
  return !Visit(get_operand(f));
}

Formula IfThenElseEliminator::VisitForall(const Formula& f) {
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
