#include "dreal/util/ibex_converter.h"

#include <algorithm>
#include <sstream>
#include <utility>

#include "dreal/util/exception.h"
#include "dreal/util/interval.h"
#include "dreal/util/logging.h"
#include "dreal/util/math.h"
#include "dreal/util/stat.h"
#include "dreal/util/timer.h"

namespace dreal {

using std::cout;
using std::ostringstream;
using std::pair;
using std::vector;

using ibex::ExprCtr;
using ibex::ExprNode;

namespace {
// A class to show statistics information at destruction.
class IbexConverterStat : public Stat {
 public:
  explicit IbexConverterStat(const bool enabled) : Stat{enabled} {}
  IbexConverterStat(const IbexConverterStat&) = default;
  IbexConverterStat(IbexConverterStat&&) = default;
  IbexConverterStat& operator=(const IbexConverterStat&) = default;
  IbexConverterStat& operator=(IbexConverterStat&&) = default;
  ~IbexConverterStat() override {
    if (enabled()) {
      using fmt::print;
      print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of Convert",
            "Ibex Converter", num_convert_);
      if (num_convert_ > 0) {
        print(cout, "{:<45} @ {:<20} = {:>15f} sec\n",
              "Total time spent in Converting", "Ibex Converter",
              timer_convert_.seconds());
      }
    }
  }

  int num_convert_{0};
  Timer timer_convert_;
};
}  // namespace

IbexConverter::IbexConverter(const vector<Variable>& variables)
    : vars_{variables} {
  // Sets up var_array_ and symbolic_var_to_ibex_var_.
  for (const Variable& var : vars_) {
    // The variable is new, we need to make one.
    DREAL_LOG_DEBUG("IbexConverter::IbexConverter: Create variable {}", var);
    const ibex::ExprSymbol* v{
        &ibex::ExprSymbol::new_(var.get_name().c_str(), ibex::Dim::scalar())};
    // Update Variable → ibex::ExprSymbol*
    symbolic_var_to_ibex_var_.emplace(var, v);
    // Update ibex::Array<const ibex::ExprSymbol>
    var_array_.add(*v);
  }
  zero_ = &ibex::ExprConstant::new_scalar(0.0);
}

IbexConverter::IbexConverter(const Box& box) : IbexConverter{box.variables()} {}

IbexConverter::~IbexConverter() {
  DREAL_LOG_DEBUG("IbexConverter::~IbexConverter()");
  if (need_to_delete_variables_) {
    for (const pair<const Variable, const ibex::ExprSymbol*>& p :
         symbolic_var_to_ibex_var_) {
      delete p.second;
    }
  }
  delete zero_;
}

const ExprCtr* IbexConverter::Convert(const Formula& f) {
  DREAL_LOG_DEBUG("IbexConverter::Convert({})", f);
  static IbexConverterStat stat{DREAL_LOG_INFO_ENABLED};
  TimerGuard timer_guard(&stat.timer_convert_, stat.enabled());
  ++stat.num_convert_;

  const ExprCtr* expr_ctr{Visit(f, true)};
  if (expr_ctr) {
    need_to_delete_variables_ = false;
  }
  return expr_ctr;
}

const ExprNode* IbexConverter::Convert(const Expression& e) {
  DREAL_LOG_DEBUG("IbexConverter::Convert({})", e);
  const ExprNode* expr_node{Visit(e)};
  if (expr_node) {
    need_to_delete_variables_ = false;
  }
  return expr_node;
}

const ibex::Array<const ibex::ExprSymbol>& IbexConverter::variables() const {
  return var_array_;
}

void IbexConverter::set_need_to_delete_variables(const bool value) {
  need_to_delete_variables_ = value;
}

const ExprNode* IbexConverter::Visit(const Expression& e) {
  return VisitExpression<const ExprNode*>(this, e);
}

const ExprNode* IbexConverter::VisitVariable(const Expression& e) {
  const Variable& var{get_variable(e)};
  auto const it = symbolic_var_to_ibex_var_.find(var);
  if (it == symbolic_var_to_ibex_var_.cend()) {
    ostringstream oss;
    oss << "Variable " << var << " is not appeared in ";
    for (const Variable& v : vars_) {
      oss << v << " ";
    }
    oss << ".";
    throw DREAL_RUNTIME_ERROR(oss.str());
  }
  return it->second;
}

const ExprNode* IbexConverter::VisitConstant(const Expression& e) {
  // Case e := c.
  // We bloat the constant c into a smallest interval [lb, ub] to avoid
  // numerical issues.
  const double c{get_constant_value(e)};
  return &ibex::ExprConstant::new_scalar(c);
}

const ExprNode* IbexConverter::VisitRealConstant(const Expression& e) {
  // Case e := [lb, ub].
  const double lb{get_lb_of_real_constant(e)};
  const double ub{get_ub_of_real_constant(e)};
  return &ibex::ExprConstant::new_scalar(ibex::Interval(lb, ub));
}

const ExprNode* IbexConverter::VisitAddition(const Expression& e) {
  const double c{get_constant_in_addition(e)};
  const ExprNode* ret{nullptr};
  if (c != 0) {
    ret = &ibex::ExprConstant::new_scalar(c);
  }
  for (const auto& p : get_expr_to_coeff_map_in_addition(e)) {
    const Expression& e_i{p.first};
    const double coeff{p.second};
    if (coeff == 1.0) {
      if (ret) {
        ret = &(*ret + *Visit(e_i));
      } else {
        ret = Visit(e_i);
      }
    } else if (coeff == -1.0) {
      if (ret) {
        ret = &(*ret - *Visit(e_i));
      } else {
        ret = Visit(-e_i);
      }
    } else {
      if (ret) {
        ret = &(*ret + coeff * *Visit(e_i));
      } else {
        ret = &(coeff * *Visit(e_i));
      }
    }
  }
  return ret;
}

const ExprNode* IbexConverter::ProcessPow(const Expression& base,
                                          const Expression& exponent) {
  // Note: IBEX provides the following four function signatures of pow
  // in "ibex_Expr.h" file. To obtain precision, we try to avoid call
  // the last one, "pow(EXPR, EXPR)".
  //
  //   1. pow(EXPR, int)
  //   2. pow(EXPR, double)
  //   3. pow(double, EXPR)
  //   4. pow(EXPR, EXPR)
  if (is_constant(exponent)) {
    const double v{get_constant_value(exponent)};
    if (is_integer(v)) {
      // Call 1. pow(EXPR, int).
      return &pow(*Visit(base), static_cast<int>(v));
    }
    if (v == 0.5) {
      // Call sqrt(base).
      return &sqrt(*Visit(base));
    } else {
      // Call 2. pow(EXPR, double).
      return &pow(*Visit(base), v);
    }
  }
  if (is_constant(base)) {
    // Call 3. pow(double, EXPR).
    const double v{get_constant_value(base)};
    return &pow(v, *Visit(exponent));
  }
  // Call 4. pow(EXPR, EXPR).
  return &pow(*Visit(base), *Visit(exponent));
}

const ExprNode* IbexConverter::VisitMultiplication(const Expression& e) {
  const double c{get_constant_in_multiplication(e)};
  const ExprNode* ret{nullptr};
  if (c != 1.0) {
    ret = &ibex::ExprConstant::new_scalar(c);
  }
  for (const auto& p : get_base_to_exponent_map_in_multiplication(e)) {
    const Expression& base{p.first};
    const Expression& exponent{p.second};
    if (ret) {
      ret = &(*ret * *ProcessPow(base, exponent));
    } else {
      ret = ProcessPow(base, exponent);
    }
  }
  return ret;
}

const ExprNode* IbexConverter::VisitDivision(const Expression& e) {
  return &(*Visit(get_first_argument(e)) / *Visit(get_second_argument(e)));
}

const ExprNode* IbexConverter::VisitLog(const Expression& e) {
  return &log(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitAbs(const Expression& e) {
  return &abs(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitExp(const Expression& e) {
  return &exp(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitSqrt(const Expression& e) {
  return &sqrt(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitPow(const Expression& e) {
  const Expression& base{get_first_argument(e)};
  const Expression& exponent{get_second_argument(e)};
  return ProcessPow(base, exponent);
}

const ExprNode* IbexConverter::VisitSin(const Expression& e) {
  return &sin(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitCos(const Expression& e) {
  return &cos(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitTan(const Expression& e) {
  return &tan(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitAsin(const Expression& e) {
  return &asin(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitAcos(const Expression& e) {
  return &acos(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitAtan(const Expression& e) {
  return &atan(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitAtan2(const Expression& e) {
  return &atan2(*Visit(get_first_argument(e)), *Visit(get_second_argument(e)));
}

const ExprNode* IbexConverter::VisitSinh(const Expression& e) {
  return &sinh(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitCosh(const Expression& e) {
  return &cosh(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitTanh(const Expression& e) {
  return &tanh(*Visit(get_argument(e)));
}

const ExprNode* IbexConverter::VisitMin(const Expression& e) {
  return &min(*Visit(get_first_argument(e)), *Visit(get_second_argument(e)));
}

const ExprNode* IbexConverter::VisitMax(const Expression& e) {
  return &max(*Visit(get_first_argument(e)), *Visit(get_second_argument(e)));
}

const ExprNode* IbexConverter::VisitIfThenElse(const Expression&) {
  throw DREAL_RUNTIME_ERROR(
      "IbexConverter: If-then-else expression is not supported yet.");
}

const ExprNode* IbexConverter::VisitUninterpretedFunction(const Expression&) {
  throw DREAL_RUNTIME_ERROR(
      "IbexConverter: Uninterpreted function is not supported.");
}

// Visits @p e and converts it into ibex::ExprNode.
const ExprCtr* IbexConverter::Visit(const Formula& f, const bool polarity) {
  return VisitFormula<const ExprCtr*>(this, f, polarity);
}

const ExprCtr* IbexConverter::VisitFalse(const Formula&, const bool) {
  throw DREAL_RUNTIME_ERROR("IbexConverter: 'False' is detected.");
}

const ExprCtr* IbexConverter::VisitTrue(const Formula&, const bool) {
  return nullptr;
}

const ExprCtr* IbexConverter::VisitVariable(const Formula&, const bool) {
  throw DREAL_RUNTIME_ERROR("IbexConverter: Boolean variable is detected.");
}

const ExprCtr* IbexConverter::VisitEqualTo(const Formula& f,
                                           const bool polarity) {
  if (polarity) {
    return &(*Visit(get_lhs_expression(f) - get_rhs_expression(f)) = *zero_);
  } else {
    return nullptr;
  }
}

const ExprCtr* IbexConverter::VisitNotEqualTo(const Formula& f,
                                              const bool polarity) {
  return VisitEqualTo(f, !polarity);
}

const ExprCtr* IbexConverter::VisitGreaterThan(const Formula& f,
                                               const bool polarity) {
  if (polarity) {
    return &(*Visit(get_lhs_expression(f) - get_rhs_expression(f)) > *zero_);
  } else {
    return &(*Visit(get_lhs_expression(f) - get_rhs_expression(f)) <= *zero_);
  }
}

const ExprCtr* IbexConverter::VisitGreaterThanOrEqualTo(const Formula& f,
                                                        const bool polarity) {
  if (polarity) {
    return &(*Visit(get_lhs_expression(f) - get_rhs_expression(f)) >= *zero_);
  } else {
    return &(*Visit(get_lhs_expression(f) - get_rhs_expression(f)) < *zero_);
  }
}

const ExprCtr* IbexConverter::VisitLessThan(const Formula& f,
                                            const bool polarity) {
  return VisitGreaterThanOrEqualTo(f, !polarity);
}

const ExprCtr* IbexConverter::VisitLessThanOrEqualTo(const Formula& f,
                                                     const bool polarity) {
  return VisitGreaterThan(f, !polarity);
}

const ExprCtr* IbexConverter::VisitConjunction(const Formula&, const bool) {
  throw DREAL_RUNTIME_ERROR("IbexConverter: A conjunction is detected.");
}

const ExprCtr* IbexConverter::VisitDisjunction(const Formula&, const bool) {
  throw DREAL_RUNTIME_ERROR("IbexConverter: A conjunction is detected.");
}

const ExprCtr* IbexConverter::VisitNegation(const Formula& f,
                                            const bool polarity) {
  return Visit(get_operand(f), !polarity);
}

const ExprCtr* IbexConverter::VisitForall(const Formula&, const bool) {
  throw DREAL_RUNTIME_ERROR(
      "IbexConverter: forall constraint is not supported.");
}

}  // namespace dreal
