#include "dreal/solver/assertion_filter.h"

#include "dreal/util/box.h"

namespace dreal {
namespace {

class AssertionFilter {
 public:
  bool Process(const Formula& f, Box* const box) const {
    return Visit(f, box, true);
  }

 public:
  bool Visit(const Formula& f, Box* const box, const bool polarity) const {
    return VisitFormula<bool>(this, f, box, polarity);
  }
  bool VisitFalse(const Formula&, Box* const, const bool) const {
    return false;
  }
  bool VisitTrue(const Formula&, Box* const, const bool) const { return false; }
  bool VisitVariable(const Formula&, Box* const, const bool) const {
    return false;
  }
  bool VisitEqualTo(const Formula& f, Box* const box,
                    const bool polarity) const {
    if (!polarity) {
      return false;
    }
    const Expression& lhs{get_lhs_expression(f)};
    const Expression& rhs{get_rhs_expression(f)};
    if (is_variable(lhs) && is_constant(rhs)) {
      // var = v
      const Variable& var{get_variable(lhs)};
      const double v{get_constant_value(rhs)};
      Box::Interval& intv{(*box)[var]};
      if (intv.contains(v)) {
        intv = v;
      } else {
        box->set_empty();
      }
      return true;
    }
    if (is_constant(lhs) && is_variable(rhs)) {
      // v = var
      const double v{get_constant_value(lhs)};
      const Variable& var{get_variable(rhs)};
      Box::Interval& intv{(*box)[var]};
      if (intv.contains(v)) {
        intv = v;
      } else {
        box->set_empty();
      }
      return true;
    }
    return false;
  }
  bool VisitNotEqualTo(const Formula& f, Box* const box,
                       const bool polarity) const {
    if (polarity) {
      return false;
    }
    const Expression& lhs{get_lhs_expression(f)};
    const Expression& rhs{get_rhs_expression(f)};
    if (is_variable(lhs) && is_constant(rhs)) {
      // var = v
      const Variable& var{get_variable(lhs)};
      const double v{get_constant_value(rhs)};
      Box::Interval& intv{(*box)[var]};
      if (intv.contains(v)) {
        intv = v;
      } else {
        box->set_empty();
      }
      return true;
    }
    if (is_constant(lhs) && is_variable(rhs)) {
      // v = var
      const double v{get_constant_value(lhs)};
      const Variable& var{get_variable(rhs)};
      Box::Interval& intv{(*box)[var]};
      if (intv.contains(v)) {
        intv = v;
      } else {
        box->set_empty();
      }
      return true;
    }
    return false;
  }
  bool VisitGreaterThan(const Formula& f, Box* const box,
                        const bool polarity) const {
    return VisitGreaterThanOrEqualTo(f, box, polarity);
  }
  bool VisitGreaterThanOrEqualTo(const Formula& f, Box* const box,
                                 const bool polarity) const {
    const Expression& lhs{get_lhs_expression(f)};
    const Expression& rhs{get_rhs_expression(f)};
    if (is_variable(lhs) && is_constant(rhs)) {
      const Variable& var{get_variable(lhs)};
      const double v{get_constant_value(rhs)};
      Box::Interval& iv{(*box)[var]};
      if (polarity) {
        // var >= v
        if (v <= iv.ub()) {
          iv = Box::Interval(v, iv.ub());
        } else {
          box->set_empty();
        }
        return true;
      } else {
        // var < v
        if (iv.lb() <= v) {
          iv = Box::Interval(iv.lb(), v);
        } else {
          box->set_empty();
        }
        return true;
      }
    }
    if (is_constant(lhs) && is_variable(rhs)) {
      const double v{get_constant_value(lhs)};
      const Variable& var{get_variable(rhs)};
      Box::Interval& iv{(*box)[var]};
      if (polarity) {
        // v >= var
        if (iv.lb() <= v) {
          iv = Box::Interval(iv.lb(), v);
        } else {
          box->set_empty();
        }
        return true;
      } else {
        // v < var
        if (v <= iv.ub()) {
          iv = Box::Interval(v, iv.ub());
        } else {
          box->set_empty();
        }
        return true;
      }
    }
    return false;
  }
  bool VisitLessThan(const Formula& f, Box* const box,
                     const bool polarity) const {
    return VisitLessThanOrEqualTo(f, box, polarity);
  }
  bool VisitLessThanOrEqualTo(const Formula& f, Box* const box,
                              const bool polarity) const {
    const Expression& lhs{get_lhs_expression(f)};
    const Expression& rhs{get_rhs_expression(f)};
    if (is_variable(lhs) && is_constant(rhs)) {
      const Variable& var{get_variable(lhs)};
      const double v{get_constant_value(rhs)};
      Box::Interval& iv{(*box)[var]};
      if (polarity) {
        // var <= v
        if (iv.lb() <= v) {
          iv = Box::Interval(iv.lb(), v);
        } else {
          box->set_empty();
        }
        return true;
      } else {
        // var > v
        if (v <= iv.ub()) {
          iv = Box::Interval(v, iv.ub());
        } else {
          box->set_empty();
        }
        return true;
      }
    }
    if (is_constant(lhs) && is_variable(rhs)) {
      const double v{get_constant_value(lhs)};
      const Variable& var{get_variable(rhs)};
      Box::Interval& iv{(*box)[var]};
      if (polarity) {
        // v <= var
        if (v <= iv.ub()) {
          iv = Box::Interval(v, iv.ub());
        } else {
          box->set_empty();
        }
        return true;
      } else {
        // v > var
        if (iv.lb() <= v) {
          iv = Box::Interval(iv.lb(), v);
        } else {
          box->set_empty();
        }
        return true;
      }
    }
    return false;
  }
  bool VisitConjunction(const Formula& f, Box* const box,
                        const bool polarity) const {
    if (!polarity) {
      return false;
    }
    // Try to simplify all. If there is a problem, need to restore the original.
    const Box saved_tmp{*box};
    bool ret{true};
    for (const Formula& f_i : get_operands(f)) {
      ret = Visit(f_i, box, polarity);
      if (!ret) {
        break;
      }
    }
    if (!ret) {
      *box = saved_tmp;
    }
    return ret;
  }
  bool VisitDisjunction(const Formula& f, Box* const box,
                        const bool polarity) const {
    if (polarity) {
      return false;
    }
    // Try to simplify all. If there is a problem, need to restore the original.
    const Box saved_tmp{*box};
    bool ret{true};
    for (const Formula& f_i : get_operands(f)) {
      ret = Visit(f_i, box, polarity);
      if (!ret) {
        break;
      }
    }
    if (!ret) {
      *box = saved_tmp;
      return false;
    }
    return ret;
  }
  bool VisitNegation(const Formula& f, Box* const box,
                     const bool polarity) const {
    return Visit(get_operand(f), box, !polarity);
  }
  bool VisitForall(const Formula&, Box* const, const bool) const {
    return false;
  }

  // Makes VisitFormula a friend of this class so that it can use private
  // operator()s.
  friend bool drake::symbolic::VisitFormula<bool>(AssertionFilter*,
                                                  const Formula&,
                                                  dreal::Box* const&,
                                                  const bool&);
};
}  // namespace

bool FilterAssertion(const Formula& assertion, Box* const box) {
  return AssertionFilter{}.Process(assertion, box);
}
}  // namespace dreal
