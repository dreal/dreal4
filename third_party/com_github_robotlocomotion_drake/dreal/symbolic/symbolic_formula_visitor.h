#pragma once

#include <utility>

#include "dreal/symbolic/symbolic_formula.h"

namespace dreal {
namespace drake {
namespace symbolic {

/// Calls visitor object @p v with a symbolic formula @p f, and arguments @p
/// args. Visitor object is expected to implement the following methods which
/// take @p f and @p args: `VisitFalse`, `VisitTrue`, `VisitVariable`,
/// `VisitEqualTo`, VisitNotEqualTo, VisitGreaterThan,
/// `VisitGreaterThanOrEqualTo`, `VisitLessThan`, `VisitLessThanOrEqualTo`,
/// `VisitConjunction`, `VisitDisjunction`, `VisitNegation`, `VisitForall`.
///
/// Check the implementation of @c NegationNormalFormConverter class in
/// symbolic/test/symbolic_formula_visitor_test.cc file to find an example.
template <typename Result, typename Visitor, typename... Args>
Result VisitFormula(Visitor* v, const Formula& f, Args&&... args) {
  switch (f.get_kind()) {
    case FormulaKind::False:
      return v->VisitFalse(f, std::forward<Args>(args)...);
    case FormulaKind::True:
      return v->VisitTrue(f, std::forward<Args>(args)...);
    case FormulaKind::Var:
      return v->VisitVariable(f, std::forward<Args>(args)...);
    case FormulaKind::Eq:
      return v->VisitEqualTo(f, std::forward<Args>(args)...);
    case FormulaKind::Neq:
      return v->VisitNotEqualTo(f, std::forward<Args>(args)...);
    case FormulaKind::Gt:
      return v->VisitGreaterThan(f, std::forward<Args>(args)...);
    case FormulaKind::Geq:
      return v->VisitGreaterThanOrEqualTo(f, std::forward<Args>(args)...);
    case FormulaKind::Lt:
      return v->VisitLessThan(f, std::forward<Args>(args)...);
    case FormulaKind::Leq:
      return v->VisitLessThanOrEqualTo(f, std::forward<Args>(args)...);
    case FormulaKind::And:
      return v->VisitConjunction(f, std::forward<Args>(args)...);
    case FormulaKind::Or:
      return v->VisitDisjunction(f, std::forward<Args>(args)...);
    case FormulaKind::Not:
      return v->VisitNegation(f, std::forward<Args>(args)...);
    case FormulaKind::Forall:
      return v->VisitForall(f, std::forward<Args>(args)...);
  }
  // Should not be reachable. But we need the following to avoid "control
  // reaches end of non-void function" gcc-warning.
  throw std::runtime_error("Should not be reachable.");
}

}  // namespace symbolic
}  // namespace drake
}  // namespace dreal
