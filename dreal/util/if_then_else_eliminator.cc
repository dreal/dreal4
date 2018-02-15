#include "dreal/util/if_then_else_eliminator.h"

#include <algorithm>  // To suppress cpplint on max.
#include <set>
#include <stdexcept>
#include <string>

#include "dreal/util/logging.h"

using std::runtime_error;
using std::set;
using std::to_string;
using std::unordered_set;

namespace dreal {
Formula IfThenElseEliminator::Process(const Formula& f) {
  Formula new_f{Visit(f)};
  if (!added_formulas_.empty()) {
    return new_f && make_conjunction(added_formulas_);
  } else {
    return f;
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
  const Variable new_var{"ITE" + to_string(counter++)};
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

namespace {

// We do not support if-then-else expressions inside of forall. This
// class is to check if this is the case.
class CheckIfThenElseInForall {
 public:
  // Checks if @p f includes if-then-else expressions or forall
  // expressions.
  bool Check(const Formula& f) { return Visit(f); }

 private:
  // Handle expressions.
  bool Visit(const Expression& e) { return VisitExpression<bool>(this, e); }
  bool VisitVariable(const Expression&) { return false; }
  bool VisitConstant(const Expression&) { return false; }
  bool VisitAddition(const Expression& e) {
    for (const auto& p : get_expr_to_coeff_map_in_addition(e)) {
      const Expression& e_i{p.first};
      if (Visit(e_i)) {
        return true;
      }
    }
    return false;
  }
  bool VisitMultiplication(const Expression& e) {
    for (const auto& p : get_base_to_exponent_map_in_multiplication(e)) {
      const Expression& e_i1{p.first};
      const Expression& e_i2{p.second};
      if (Visit(e_i1) || Visit(e_i2)) {
        return true;
      }
    }
    return false;
  }
  bool VisitDivision(const Expression& e) {
    return Visit(get_first_argument(e)) || Visit(get_second_argument(e));
  }
  bool VisitLog(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitAbs(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitExp(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitSqrt(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitPow(const Expression& e) {
    return Visit(get_first_argument(e)) || Visit(get_second_argument(e));
  }
  bool VisitSin(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitCos(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitTan(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitAsin(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitAcos(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitAtan(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitAtan2(const Expression& e) {
    return Visit(get_first_argument(e)) || Visit(get_second_argument(e));
  }
  bool VisitSinh(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitCosh(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitTanh(const Expression& e) { return Visit(get_argument(e)); }
  bool VisitMin(const Expression& e) {
    return Visit(get_first_argument(e)) || Visit(get_second_argument(e));
  }
  bool VisitMax(const Expression& e) {
    return Visit(get_first_argument(e)) || Visit(get_second_argument(e));
  }
  bool VisitIfThenElse(const Expression&) { return true; }
  bool VisitUninterpretedFunction(const Expression&) { return false; }

  // Handle formula
  bool Visit(const Formula& f) { return VisitFormula<bool>(this, f); }
  bool VisitFalse(const Formula&) { return false; }
  bool VisitTrue(const Formula&) { return false; }
  bool VisitVariable(const Formula&) { return false; }
  bool VisitEqualTo(const Formula& f) {
    return Visit(get_lhs_expression(f)) || Visit(get_rhs_expression(f));
  }
  bool VisitNotEqualTo(const Formula& f) {
    return Visit(get_lhs_expression(f)) || Visit(get_rhs_expression(f));
  }
  bool VisitGreaterThan(const Formula& f) {
    return Visit(get_lhs_expression(f)) || Visit(get_rhs_expression(f));
  }
  bool VisitGreaterThanOrEqualTo(const Formula& f) {
    return Visit(get_lhs_expression(f)) || Visit(get_rhs_expression(f));
  }
  bool VisitLessThan(const Formula& f) {
    return Visit(get_lhs_expression(f)) || Visit(get_rhs_expression(f));
  }
  bool VisitLessThanOrEqualTo(const Formula& f) {
    return Visit(get_lhs_expression(f)) || Visit(get_rhs_expression(f));
  }
  bool VisitConjunction(const Formula& f) {
    for (const Formula& f_i : get_operands(f)) {
      if (Visit(f_i)) {
        return true;
      }
    }
    return false;
  }
  bool VisitDisjunction(const Formula& f) {
    for (const Formula& f_i : get_operands(f)) {
      if (Visit(f_i)) {
        return true;
      }
    }
    return false;
  }
  bool VisitNegation(const Formula& f) { return Visit(get_operand(f)); }
  bool VisitForall(const Formula&) { return true; }

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend bool drake::symbolic::VisitFormula<bool>(CheckIfThenElseInForall*,
                                                  const Formula&);
  // Makes VisitExpression a friend of this class so that it can use private
  // operator()s.
  friend bool drake::symbolic::VisitExpression<bool>(CheckIfThenElseInForall*,
                                                     const Expression&);
};

}  // namespace

Formula IfThenElseEliminator::VisitForall(const Formula& f) {
  //
  // f := forall(v₁, ... vₙ, f')
  //
  // ∃x.∀y. ITE(ψ(x, y), f₁(x, y), f₂(x, y)) > 0 can be translated into
  //
  //     ∃x.∀y.∃v. (v > 0) ∧ [ψ(x, y) ⇒ (v = f₁(x, y))]
  //                       ∧ [¬ψ(x, y) ⇒ (v = f₂(x, y))]
  //
  //     ∃x.∀y.∀v. [(ψ(x, y) ∧ (v = f₁(x, y))) ⇒ (v > 0)] ∧
  //               [(¬ψ(x, y) ∧ (v = f₂(x, y))) ⇒ (v > 0)]
  //                       ∧ [¬ψ(x, y) ⇒ (v = f₂(x, y))]
  //
  if (CheckIfThenElseInForall{}.Check(get_quantified_formula(f))) {
    DREAL_LOG_ERROR(
        "{} includes either nested forall quantifiers or if-then-else inside "
        "of quantifiers. We do not support these formula yet.",
        f);
    throw runtime_error("Not yet supported.");
  }
  return f;
}

}  // namespace dreal
