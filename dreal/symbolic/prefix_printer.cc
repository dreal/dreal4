#include "dreal/symbolic/prefix_printer.h"

#include <limits>
#include <sstream>
#include <stdexcept>

using std::ostream;
using std::ostringstream;
using std::runtime_error;
using std::string;

namespace dreal {

PrefixPrinter::PrefixPrinter(ostream& os)
    : os_{os}, old_precision_{os.precision()} {
  // See
  // https://stackoverflow.com/questions/554063/how-do-i-print-a-double-value-with-full-precision-using-cout#comment40126260_554134.
  os_.precision(std::numeric_limits<double>::max_digits10 + 2);
}

PrefixPrinter::~PrefixPrinter() { os_.precision(old_precision_); }

ostream& PrefixPrinter::Print(const Expression& e) {
  return VisitExpression<ostream&>(this, e);
}

ostream& PrefixPrinter::Print(const Formula& f) {
  return VisitFormula<ostream&>(this, f);
}

ostream& PrefixPrinter::VisitVariable(const Expression& e) {
  return os_ << get_variable(e);
}

ostream& PrefixPrinter::VisitConstant(const Expression& e) {
  return os_ << get_constant_value(e);
}

ostream& PrefixPrinter::VisitRealConstant(const Expression& e) {
  const double mid{get_lb_of_real_constant(e) / 2.0 +
                   get_ub_of_real_constant(e) / 2.0};
  return os_ << mid;
}

ostream& PrefixPrinter::VisitUnaryFunction(const std::string& name,
                                           const Expression& e) {
  os_ << "(" << name << " ";
  Print(get_argument(e));
  return os_ << ")";
}

ostream& PrefixPrinter::VisitBinaryFunction(const std::string& name,
                                            const Expression& e) {
  os_ << "(" << name << " ";
  Print(get_first_argument(e));
  os_ << " ";
  Print(get_second_argument(e));
  return os_ << ")";
}

ostream& PrefixPrinter::VisitAddition(const Expression& e) {
  const double constant{get_constant_in_addition(e)};
  os_ << "(+";
  if (constant != 0.0) {
    os_ << " " << constant;
  }
  for (const auto& p : get_expr_to_coeff_map_in_addition(e)) {
    const Expression& e_i{p.first};
    const double c_i{p.second};
    os_ << " ";
    if (c_i == 1.0) {
      Print(e_i);
    } else {
      os_ << "(* " << c_i << " ";
      Print(e_i);
      os_ << ")";
    }
  }
  return os_ << ")";
}

ostream& PrefixPrinter::VisitMultiplication(const Expression& e) {
  const double constant{get_constant_in_multiplication(e)};
  os_ << "(*";
  if (constant != 1.0) {
    os_ << " " << constant;
  }
  for (const auto& p : get_base_to_exponent_map_in_multiplication(e)) {
    const Expression& b_i{p.first};
    const Expression& e_i{p.second};
    os_ << " ";
    if (is_one(e_i)) {
      Print(b_i);
    } else {
      os_ << "(^ ";
      Print(b_i);
      os_ << " ";
      Print(e_i);
      os_ << ")";
    }
  }
  return os_ << ")";
}

ostream& PrefixPrinter::VisitDivision(const Expression& e) {
  return VisitBinaryFunction("/", e);
}

ostream& PrefixPrinter::VisitLog(const Expression& e) {
  return VisitUnaryFunction("log", e);
}

ostream& PrefixPrinter::VisitAbs(const Expression& e) {
  return VisitUnaryFunction("abs", e);
}

ostream& PrefixPrinter::VisitExp(const Expression& e) {
  return VisitUnaryFunction("exp", e);
}

ostream& PrefixPrinter::VisitSqrt(const Expression& e) {
  return VisitUnaryFunction("sqrt", e);
}

ostream& PrefixPrinter::VisitPow(const Expression& e) {
  return VisitBinaryFunction("^", e);
}

ostream& PrefixPrinter::VisitSin(const Expression& e) {
  return VisitUnaryFunction("sin", e);
}

ostream& PrefixPrinter::VisitCos(const Expression& e) {
  return VisitUnaryFunction("cos", e);
}

ostream& PrefixPrinter::VisitTan(const Expression& e) {
  return VisitUnaryFunction("tan", e);
}

ostream& PrefixPrinter::VisitAsin(const Expression& e) {
  return VisitUnaryFunction("asin", e);
}

ostream& PrefixPrinter::VisitAcos(const Expression& e) {
  return VisitUnaryFunction("acos", e);
}

ostream& PrefixPrinter::VisitAtan(const Expression& e) {
  return VisitUnaryFunction("atan", e);
}

ostream& PrefixPrinter::VisitAtan2(const Expression& e) {
  return VisitBinaryFunction("atan2", e);
}

ostream& PrefixPrinter::VisitSinh(const Expression& e) {
  return VisitUnaryFunction("sinh", e);
}

ostream& PrefixPrinter::VisitCosh(const Expression& e) {
  return VisitUnaryFunction("cosh", e);
}

ostream& PrefixPrinter::VisitTanh(const Expression& e) {
  return VisitUnaryFunction("tanh", e);
}

ostream& PrefixPrinter::VisitMin(const Expression& e) {
  return VisitBinaryFunction("min", e);
}

ostream& PrefixPrinter::VisitMax(const Expression& e) {
  return VisitBinaryFunction("max", e);
}

ostream& PrefixPrinter::VisitIfThenElse(const Expression& e) {
  os_ << "(ite ";
  Print(get_conditional_formula(e));
  os_ << " ";
  Print(get_then_expression(e));
  os_ << " ";
  Print(get_else_expression(e));
  return os_ << ")";
}

ostream& PrefixPrinter::VisitUninterpretedFunction(const Expression&) {
  throw runtime_error("Not implemented.");
}

ostream& PrefixPrinter::VisitFalse(const Formula&) { return os_ << "false"; }

ostream& PrefixPrinter::VisitTrue(const Formula&) { return os_ << "true"; }

ostream& PrefixPrinter::VisitVariable(const Formula& f) {
  return os_ << get_variable(f);
}

ostream& PrefixPrinter::VisitEqualTo(const Formula& f) {
  os_ << "(= ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << ")";
}

ostream& PrefixPrinter::VisitNotEqualTo(const Formula& f) {
  os_ << "(not (= ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << "))";
}

ostream& PrefixPrinter::VisitGreaterThan(const Formula& f) {
  os_ << "(> ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << ")";
}

ostream& PrefixPrinter::VisitGreaterThanOrEqualTo(const Formula& f) {
  os_ << "(>= ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << ")";
}

ostream& PrefixPrinter::VisitLessThan(const Formula& f) {
  os_ << "(< ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << ")";
}

ostream& PrefixPrinter::VisitLessThanOrEqualTo(const Formula& f) {
  os_ << "(<= ";
  Print(get_lhs_expression(f));
  os_ << " ";
  Print(get_rhs_expression(f));
  return os_ << ")";
}

ostream& PrefixPrinter::VisitConjunction(const Formula& f) {
  os_ << "(and";
  for (const auto& f_i : get_operands(f)) {
    os_ << " ";
    Print(f_i);
  }
  return os_ << ")";
}

ostream& PrefixPrinter::VisitDisjunction(const Formula& f) {
  os_ << "(or";
  for (const auto& f_i : get_operands(f)) {
    os_ << " ";
    Print(f_i);
  }
  return os_ << ")";
}

ostream& PrefixPrinter::VisitNegation(const Formula& f) {
  os_ << "(not ";
  Print(get_operand(f));
  return os_ << ")";
}

ostream& PrefixPrinter::VisitForall(const Formula&) {
  throw runtime_error("Not implemented.");
}

string ToPrefix(const Expression& e) {
  ostringstream oss;
  PrefixPrinter pp{oss};
  pp.Print(e);
  return oss.str();
}

string ToPrefix(const Formula& f) {
  ostringstream oss;
  PrefixPrinter pp{oss};
  pp.Print(f);
  return oss.str();
}

}  // namespace dreal
