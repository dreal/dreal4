#include "dreal/solver/assertion_filter.h"

#include <cmath>

#include "dreal/util/box.h"
#include "dreal/util/exception.h"

namespace dreal {
namespace {

using std::nextafter;

// Constrains the @p box with ` box[var].lb() == v`.
FilterAssertionResult UpdateBoundsViaEquality(const Variable& var,
                                              const double v, Box* const box) {
  Box::Interval& intv{(*box)[var]};
  if (intv.lb() == intv.ub() && intv.lb() == v) {
    return FilterAssertionResult::FilteredWithoutChange;
  }
  if (intv.contains(v)) {
    intv = v;
  } else {
    box->set_empty();
  }
  return FilterAssertionResult::FilteredWithChange;
}

// Constrains the @p box with ` box[var].lb() >= v`.
FilterAssertionResult UpdateLowerBound(const Variable& var, const double v,
                                       Box* const box) {
  Box::Interval& iv{(*box)[var]};
  if (v <= iv.lb()) {
    return FilterAssertionResult::FilteredWithoutChange;
  }
  if (v <= iv.ub()) {
    iv = Box::Interval(v, iv.ub());
  } else {
    box->set_empty();
  }
  return FilterAssertionResult::FilteredWithChange;
}

// Constrains the @p box with `box[var].lb() > v`. It turns the strict
// inequality into a non-strict one, `box[var].lb() >= v + ε` where `v
// + ε` is the smallest representable floating-point number bigger than
// `v`.
FilterAssertionResult UpdateStrictLowerBound(const Variable& var,
                                             const double v, Box* const box) {
  return UpdateLowerBound(var, nextafter(v, DBL_MAX), box);
}

// Constrains the @p box with ` box[var].lb() <= v`.
FilterAssertionResult UpdateUpperBound(const Variable& var, const double v,
                                       Box* const box) {
  Box::Interval& iv{(*box)[var]};
  if (v >= iv.ub()) {
    return FilterAssertionResult::FilteredWithoutChange;
  }
  if (v >= iv.lb()) {
    iv = Box::Interval(iv.lb(), v);
  } else {
    box->set_empty();
  }
  return FilterAssertionResult::FilteredWithChange;
}

// Constrains the @p box with `box[var].lb() < v`. It turns the strict
// inequality into a non-strict one, `box[var].lb() <= v - ε` where `v
// - ε` is the largest representable floating-point number smaller
// than `v`.
FilterAssertionResult UpdateStrictUpperBound(const Variable& var,
                                             const double v, Box* const box) {
  return UpdateUpperBound(var, nextafter(v, DBL_MIN), box);
}

class AssertionFilter {
 public:
  FilterAssertionResult Process(const Formula& f, Box* const box) const {
    return Visit(f, box, true);
  }

 public:
  FilterAssertionResult Visit(const Formula& f, Box* const box,
                              const bool polarity) const {
    return VisitFormula<FilterAssertionResult>(this, f, box, polarity);
  }
  FilterAssertionResult VisitFalse(const Formula&, Box* const,
                                   const bool) const {
    return FilterAssertionResult::NotFiltered;
  }
  FilterAssertionResult VisitTrue(const Formula&, Box* const,
                                  const bool) const {
    return FilterAssertionResult::NotFiltered;
  }
  FilterAssertionResult VisitVariable(const Formula&, Box* const,
                                      const bool) const {
    return FilterAssertionResult::NotFiltered;
  }
  FilterAssertionResult VisitEqualTo(const Formula& f, Box* const box,
                                     const bool polarity) const {
    if (!polarity) {
      return FilterAssertionResult::NotFiltered;
    }
    const Expression& lhs{get_lhs_expression(f)};
    const Expression& rhs{get_rhs_expression(f)};
    if (is_variable(lhs) && is_constant(rhs)) {
      // var = v
      const Variable& var{get_variable(lhs)};
      const double v{get_constant_value(rhs)};
      return UpdateBoundsViaEquality(var, v, box);
    }
    if (is_constant(lhs) && is_variable(rhs)) {
      // v = var
      const double v{get_constant_value(lhs)};
      const Variable& var{get_variable(rhs)};
      return UpdateBoundsViaEquality(var, v, box);
    }
    return FilterAssertionResult::NotFiltered;
  }
  FilterAssertionResult VisitNotEqualTo(const Formula& f, Box* const box,
                                        const bool polarity) const {
    // Because (x != y) is !(x == y).
    return VisitEqualTo(f, box, !polarity);
  }
  FilterAssertionResult VisitGreaterThan(const Formula& f, Box* const box,
                                         const bool polarity) const {
    const Expression& lhs{get_lhs_expression(f)};
    const Expression& rhs{get_rhs_expression(f)};
    if (is_variable(lhs) && is_constant(rhs)) {
      const Variable& var{get_variable(lhs)};
      const double v{get_constant_value(rhs)};
      if (polarity) {
        // var > v
        return UpdateStrictLowerBound(var, v, box);
      } else {
        // var <= v
        return UpdateUpperBound(var, v, box);
      }
    }
    if (is_constant(lhs) && is_variable(rhs)) {
      const double v{get_constant_value(lhs)};
      const Variable& var{get_variable(rhs)};
      if (polarity) {
        // v > var
        return UpdateStrictUpperBound(var, v, box);
      } else {
        // v <= var
        return UpdateLowerBound(var, v, box);
      }
    }
    return FilterAssertionResult::NotFiltered;
  }
  FilterAssertionResult VisitGreaterThanOrEqualTo(const Formula& f,
                                                  Box* const box,
                                                  const bool polarity) const {
    const Expression& lhs{get_lhs_expression(f)};
    const Expression& rhs{get_rhs_expression(f)};
    if (is_variable(lhs) && is_constant(rhs)) {
      const Variable& var{get_variable(lhs)};
      const double v{get_constant_value(rhs)};
      if (polarity) {
        // var >= v
        return UpdateLowerBound(var, v, box);
      } else {
        // var < v
        return UpdateStrictUpperBound(var, v, box);
      }
    }
    if (is_constant(lhs) && is_variable(rhs)) {
      const double v{get_constant_value(lhs)};
      const Variable& var{get_variable(rhs)};
      if (polarity) {
        // v >= var
        return UpdateUpperBound(var, v, box);
      } else {
        // v < var
        return UpdateStrictLowerBound(var, v, box);
      }
    }
    return FilterAssertionResult::NotFiltered;
  }
  FilterAssertionResult VisitLessThan(const Formula& f, Box* const box,
                                      const bool polarity) const {
    // Because x < y is !(x >= y).
    return VisitGreaterThanOrEqualTo(f, box, !polarity);
  }
  FilterAssertionResult VisitLessThanOrEqualTo(const Formula& f, Box* const box,
                                               const bool polarity) const {
    // Because x <= y is !(x > y).
    return VisitGreaterThan(f, box, !polarity);
  }
  FilterAssertionResult VisitConjunction(const Formula&, Box* const,
                                         const bool) const {
    DREAL_UNREACHABLE();
  }
  FilterAssertionResult VisitDisjunction(const Formula&, Box* const,
                                         const bool) const {
    DREAL_UNREACHABLE();
  }
  FilterAssertionResult VisitNegation(const Formula& f, Box* const box,
                                      const bool polarity) const {
    return Visit(get_operand(f), box, !polarity);
  }
  FilterAssertionResult VisitForall(const Formula&, Box* const,
                                    const bool) const {
    return FilterAssertionResult::NotFiltered;
  }

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend FilterAssertionResult
  drake::symbolic::VisitFormula<FilterAssertionResult>(AssertionFilter*,
                                                       const Formula&,
                                                       dreal::Box* const&,
                                                       const bool&);
};
}  // namespace

FilterAssertionResult FilterAssertion(const Formula& assertion,
                                      Box* const box) {
  return AssertionFilter{}.Process(assertion, box);
}
}  // namespace dreal
