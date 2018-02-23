#include "dreal/smt2/term.h"

#include <stdexcept>
#include <utility>

#include "dreal/util/exception.h"

namespace dreal {

using std::move;
using std::ostream;
using std::runtime_error;

Term::Term(Expression e) : type_{Term::Type::EXPRESSION}, e_{move(e)} {}
Term::Term(Formula f) : type_{Term::Type::FORMULA}, f_{move(f)} {}

Term::Type Term::type() const { return type_; }

const Expression& Term::expression() const {
  if (type() != Term::Type::EXPRESSION) {
    throw runtime_error("This term is not an expression.");
  }
  return e_;
}

Expression& Term::mutable_expression() {
  return const_cast<Expression&>(expression());
}

const Formula& Term::formula() const {
  if (type() != Term::Type::FORMULA) {
    throw runtime_error("This term is not a formula.");
  }
  return f_;
}

Formula& Term::mutable_formula() { return const_cast<Formula&>(formula()); }

ostream& operator<<(ostream& os, const Term& t) {
  switch (t.type()) {
    case Term::Type::EXPRESSION:
      return os << t.expression();
    case Term::Type::FORMULA:
      return os << t.formula();
  }
  DREAL_UNREACHABLE();
}

}  // namespace dreal
