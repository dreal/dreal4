#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "fmt/format.h"
#include "fmt/ostream.h"
#include "pybind11/operators.h"
#include "pybind11/pybind11.h"
#include "pybind11/stl.h"

#include "dreal/api/api.h"
#include "dreal/smt2/logic.h"
#include "dreal/solver/config.h"
#include "dreal/solver/context.h"
#include "dreal/symbolic/prefix_printer.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/logging.h"
#include "dreal/util/optional.h"

#if defined __clang__
#if __has_warning("-Wself-assign-overloaded")
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wself-assign-overloaded"
#endif
#endif

namespace pybind11 {
namespace detail {
// Need this specialization to make optional<Box> working.
template <>
struct type_caster<dreal::optional<dreal::Box>>
    : public optional_caster<dreal::optional<dreal::Box>> {};
}  // namespace detail
}  // namespace pybind11

namespace dreal {

using std::pair;
using std::string;
using std::vector;

// NOLINTNEXTLINE(build/namespaces)
namespace py = pybind11;

PYBIND11_MODULE(_dreal_py, m) {
  m.doc() = "dReal Python Module";

  py::class_<Box::Interval>(m, "Interval")
      .def(py::init<>())
      .def(py::init<double, double>())
      .def(py::init<double>())
      .def(py::self == py::self)
      .def(py::self != py::self)
      .def("__str__",
           [](const Box::Interval& self) { return fmt::format("{}", self); })
      .def("__repr__",
           [](const Box::Interval& self) {
             return fmt::format("Interval({}, {})", self.lb(), self.ub());
           })
      .def(py::self & py::self)
      .def(py::self &= py::self)
      .def(py::self | py::self)
      .def(py::self |= py::self)
      .def("is_empty", &Box::Interval::is_empty)
      .def("set_empty", &Box::Interval::set_empty)
      .def("inflate", py::overload_cast<double>(&Box::Interval::inflate))
      .def("inflate",
           py::overload_cast<double, double>(&Box::Interval::inflate))
      .def("lb", &Box::Interval::lb)
      .def("ub", &Box::Interval::ub)
      .def("mid", &Box::Interval::mid)
      .def("rad", &Box::Interval::rad)
      .def("diam", &Box::Interval::diam)
      .def("mig", &Box::Interval::mig)
      .def("mag", &Box::Interval::mag)
      .def("is_subset", &Box::Interval::is_subset)
      .def("is_strict_subset", &Box::Interval::is_strict_subset)
      .def("is_interior_subset", &Box::Interval::is_interior_subset)
      .def("is_relative_interior_subset",
           &Box::Interval::is_relative_interior_subset)
      .def("is_strict_interior_subset",
           &Box::Interval::is_strict_interior_subset)
      .def("is_superset", &Box::Interval::is_superset)
      .def("is_strict_superset", &Box::Interval::is_strict_superset)
      .def("contains", &Box::Interval::contains)
      .def("__contains__", &Box::Interval::contains)
      .def("interior_contains", &Box::Interval::interior_contains)
      .def("intersects", &Box::Interval::intersects)
      .def("overlaps", &Box::Interval::overlaps)
      .def("is_disjoint", &Box::Interval::is_disjoint)
      .def("is_degenerated", &Box::Interval::is_degenerated)
      .def("is_unbounded", &Box::Interval::is_unbounded)
      .def("is_bisectable", &Box::Interval::is_bisectable)
      .def("rel_distance", &Box::Interval::rel_distance)
      .def("complementary", &Box::Interval::complementary)
      .def("diff", &Box::Interval::diff)
      .def("div2_inter",
           py::overload_cast<const Box::Interval&, const Box::Interval&,
                             Box::Interval&>(&Box::Interval::div2_inter))
      .def("div2_inter",
           py::overload_cast<const Box::Interval&, const Box::Interval&>(
               &Box::Interval::div2_inter))
      .def("bisect", &Box::Interval::bisect)
      .def_readonly_static("PI", &Box::Interval::PI)
      .def_readonly_static("TWO_PI", &Box::Interval::TWO_PI)
      .def_readonly_static("HALF_PI", &Box::Interval::HALF_PI)
      .def_readonly_static("EMPTY_SET", &Box::Interval::EMPTY_SET)
      .def_readonly_static("ALL_REALS", &Box::Interval::ALL_REALS)
      .def_readonly_static("ZERO", &Box::Interval::ZERO)
      .def_readonly_static("ONE", &Box::Interval::ONE)
      .def_readonly_static("POS_REALS", &Box::Interval::POS_REALS)
      .def_readonly_static("NEG_REALS", &Box::Interval::NEG_REALS)
      // Unary Minus.
      .def(-py::self)
      // Addition.
      .def(py::self + py::self)
      .def(py::self + double())
      .def(double() + py::self)
      .def(py::self += py::self)
      .def(py::self += double())
      // Subtraction.
      .def(py::self - py::self)
      .def(py::self - double())
      .def(double() - py::self)
      .def(py::self -= py::self)
      .def(py::self -= double())
      // Multiplication.
      .def(py::self * py::self)
      .def(py::self * double())
      .def(double() * py::self)
      .def(py::self *= py::self)
      .def(py::self *= double())
      // Division.
      .def(py::self / py::self)
      .def(py::self / double())
      .def(double() / py::self)
      .def(py::self /= py::self)
      .def(py::self /= double());

  m.def("div2",
        [](const Box::Interval& x, const Box::Interval& y, Box::Interval& out1,
           Box::Interval& out2) { return div2(x, y, out1, out2); })
      .def("distance", [](const Box::Interval& i1,
                          const Box::Interval& i2) { return distance(i1, i2); })
      .def("sqr", [](const Box::Interval& i) { return sqr(i); })
      .def("sqrt", [](const Box::Interval& i) { return sqrt(i); })
      .def("pow", [](const Box::Interval& x, const int n) { return pow(x, n); })
      .def("pow",
           [](const Box::Interval& x, const double n) { return pow(x, n); })
      .def("pow", [](const Box::Interval& x,
                     const Box::Interval& n) { return pow(x, n); })
      .def("root",
           [](const Box::Interval& x, const int n) { return root(x, n); })
      .def("exp", [](const Box::Interval& i) { return exp(i); })
      .def("log", [](const Box::Interval& i) { return log(i); })
      .def("cos", [](const Box::Interval& i) { return cos(i); })
      .def("tan", [](const Box::Interval& i) { return tan(i); })
      .def("sin", [](const Box::Interval& i) { return sin(i); })
      .def("acos", [](const Box::Interval& i) { return acos(i); })
      .def("asin", [](const Box::Interval& i) { return asin(i); })
      .def("atan", [](const Box::Interval& i) { return atan(i); })
      .def("atan2", [](const Box::Interval& i1,
                       const Box::Interval& i2) { return atan2(i1, i2); })
      .def("cosh", [](const Box::Interval& i) { return cosh(i); })
      .def("sinh", [](const Box::Interval& i) { return sinh(i); })
      .def("tanh", [](const Box::Interval& i) { return tanh(i); })
      .def("acosh", [](const Box::Interval& i) { return acosh(i); })
      .def("asinh", [](const Box::Interval& i) { return asinh(i); })
      .def("atanh", [](const Box::Interval& i) { return atanh(i); })
      .def("abs", [](const Box::Interval& i) { return abs(i); })
      .def("max", [](const Box::Interval& i1,
                     const Box::Interval& i2) { return max(i1, i2); })
      .def("min", [](const Box::Interval& i1,
                     const Box::Interval& i2) { return min(i1, i2); })
      .def("sign", [](const Box::Interval& x) { return sign(x); })
      .def("integer", [](const Box::Interval& x) { return integer(x); });

  py::class_<Box>(m, "Box")
      .def(py::init<const vector<Variable>&>())
      .def("Add", py::overload_cast<const Variable&>(&Box::Add))
      .def("Add", py::overload_cast<const Variable&, double, double>(&Box::Add))
      .def("empty", &Box::empty)
      .def("set_empty", &Box::set_empty)
      .def("size", &Box::size)
      .def("__setitem__", [](Box& self, const Variable& var,
                             const Box::Interval& i) { self[var] = i; })
      .def("__setitem__", [](Box& self, const int idx,
                             const Box::Interval& i) { self[idx] = i; })
      .def("__getitem__",
           [](const Box& self, const Variable& var) { return self[var]; })
      .def("__getitem__",
           [](const Box& self, const int idx) { return self[idx]; })
      .def("__repr__",
           [](const Box& self) { return fmt::format("<Box \"{}\">", self); })
      .def("__len__", &Box::size)
      .def("__delitem__",
           [](const Box& self, const Variable& var) {
             throw std::runtime_error{
                 "Box class does not allow deleting an item"};
           })
      .def("clear",
           [](const Box& self) {
             throw std::runtime_error{
                 "Box class does not support the 'clear' operation"};
           })
      .def("has_key",
           [](const Box& self, const Variable& var) {
             return self.has_variable(var);
           })
      .def("keys", [](const Box& self) { return self.variables(); })
      .def("values",
           [](const Box& self) {
             const ibex::IntervalVector& iv{self.interval_vector()};
             vector<ibex::Interval> ret;
             ret.reserve(iv.size());
             for (int i = 0; i < iv.size(); ++i) {
               ret.push_back(iv[i]);
             }
             return ret;
           })
      .def("items",
           [](const Box& self) {
             const vector<Variable>& vars{self.variables()};
             const ibex::IntervalVector& iv{self.interval_vector()};
             vector<pair<Variable, ibex::Interval>> ret;
             ret.reserve(iv.size());
             for (int i = 0; i < iv.size(); ++i) {
               ret.emplace_back(vars[i], iv[i]);
             }
             return ret;
           })
      .def("variable", &Box::variable)
      .def("index", &Box::index)
      .def("MaxDiam", &Box::MaxDiam)
      .def("bisect",
           [](const Box& self, const int i) { return self.bisect(i); })
      .def("bisect", [](const Box& self,
                        const Variable& var) { return self.bisect(var); })
      .def("InplaceUnion", &Box::InplaceUnion)
      .def(py::self == py::self)
      .def(py::self != py::self)
      .def("__str__", [](const Box& self) { return fmt::format("{}", self); });

  py::class_<Variable> variable(m, "Variable");
  variable.def(py::init<const string&>())
      .def(py::init<const string&, Variable::Type>())
      .def("get_id", &Variable::get_id)
      .def("get_type", &Variable::get_type)
      .def("__str__", &Variable::to_string)
      .def("__repr__",
           [](const Variable& self) {
             return fmt::format("Variable('{}')", self.to_string());
           })
      .def("__hash__",
           [](const Variable& self) { return std::hash<Variable>{}(self); })
      // Addition.
      .def(py::self + py::self)
      .def(py::self + double())
      .def(double() + py::self)
      // Subtraction.
      .def(py::self - py::self)
      .def(py::self - double())
      .def(double() - py::self)
      // Multiplication.
      .def(py::self * py::self)
      .def(py::self * double())
      .def(double() * py::self)
      // Division.
      .def(py::self / py::self)
      .def(py::self / double())
      .def(double() / py::self)
      // Pow.
      .def("__pow__",
           [](const Variable& self, const Expression& other) {
             return pow(self, other);
           },
           py::is_operator())
      // Unary Plus.
      .def(+py::self)
      // Unary Minus.
      .def(-py::self)
      // LT(<).
      // Note that for `double < Variable` case, the reflected op ('>' in this
      // case) is called. For example, `1 < x` will return `x > 1`.
      .def(py::self < Expression())
      .def(py::self < py::self)
      .def(py::self < double())
      // LE(<=).
      .def(py::self <= Expression())
      .def(py::self <= py::self)
      .def(py::self <= double())
      // GT(>).
      .def(py::self > Expression())
      .def(py::self > py::self)
      .def(py::self > double())
      // GE(>=).
      .def(py::self >= Expression())
      .def(py::self >= py::self)
      .def(py::self >= double())
      // EQ(==).
      .def(py::self == Expression())
      .def(py::self == py::self)
      .def(py::self == double())
      // NE(!=).
      .def(py::self != Expression())
      .def(py::self != py::self)
      .def(py::self != double());

  py::enum_<Variable::Type>(variable, "Type")
      .value("Real", Variable::Type::CONTINUOUS)
      .value("Int", Variable::Type::INTEGER)
      .value("Bool", Variable::Type::BOOLEAN)
      .value("Binary", Variable::Type::BINARY)
      .export_values();

  py::class_<Variables>(m, "Variables")
      .def(py::init<>())
      .def(py::init([](const std::vector<Variable>& vec) {
        Variables variables;
        variables.insert(vec.begin(), vec.end());
        return variables;
      }))
      .def("size", &Variables::size)
      .def("__len__", &Variables::size)
      .def("empty", &Variables::empty)
      .def("__str__", &Variables::to_string)
      .def("__repr__",
           [](const Variables& self) {
             return fmt::format("<Variables \"{}\">", self);
           })
      .def("to_string", &Variables::to_string)
      .def("__hash__",
           [](const Variables& self) { return hash_value<Variables>{}(self); })
      .def("insert",
           [](Variables& self, const Variable& var) { self.insert(var); })
      .def("insert",
           [](Variables& self, const Variables& vars) { self.insert(vars); })
      .def("erase",
           [](Variables& self, const Variable& var) { return self.erase(var); })
      .def("erase", [](Variables& self,
                       const Variables& vars) { return self.erase(vars); })
      .def("include", &Variables::include)
      .def("__contains__", &Variables::include)
      .def("IsSubsetOf", &Variables::IsSubsetOf)
      .def("IsSupersetOf", &Variables::IsSupersetOf)
      .def("IsStrictSubsetOf", &Variables::IsStrictSubsetOf)
      .def("IsStrictSupersetOf", &Variables::IsStrictSupersetOf)
      .def("__iter__",
           [](const Variables& vars) {
             return py::make_iterator(vars.begin(), vars.end());
           },
           py::keep_alive<
               0, 1>() /* Essential: keep object alive while iterator exists */)
      .def(py::self == py::self)
      .def(py::self < py::self)
      .def(py::self + py::self)
      .def(py::self + Variable())
      .def(Variable() + py::self)
      .def(py::self - py::self)
      .def(py::self - Variable());

  m.def("intersect", [](const Variables& vars1, const Variables& vars2) {
    return intersect(vars1, vars2);
  });

  py::class_<Expression>(m, "Expression")
      .def(py::init<>())
      .def(py::init<double>())
      .def(py::init<const Variable&>())
      .def("__str__", &Expression::to_string)
      .def("__repr__",
           [](const Expression& self) {
             return fmt::format("<Expression \"{}\">", self.to_string());
           })
      .def("to_string", &Expression::to_string)
      .def("Expand", &Expression::Expand)
      .def("Evaluate", [](const Expression& self) { return self.Evaluate(); })
      .def("Evaluate",
           [](const Expression& self, const Environment::map& env) {
             Environment e;
             return self.Evaluate(Environment{env});
           })
      .def("EvaluatePartial",
           [](const Expression& self, const Environment::map& env) {
             return self.EvaluatePartial(Environment{env});
           })
      .def("Substitute",
           [](const Expression& self, const Variable& var,
              const Expression& e) { return self.Substitute(var, e); })
      .def("Substitute",
           [](const Expression& self, const ExpressionSubstitution& s) {
             return self.Substitute(s);
           })
      .def("Substitute",
           [](const Expression& self, const FormulaSubstitution& s) {
             return self.Substitute(s);
           })
      .def("Substitute",
           [](const Expression& self, const ExpressionSubstitution& expr_subst,
              const FormulaSubstitution& formula_subst) {
             return self.Substitute(expr_subst, formula_subst);
           })
      // Addition
      .def(py::self + py::self)
      .def(py::self + Variable())
      .def(py::self + double())
      .def(Variable() + py::self)
      .def(double() + py::self)
      .def(py::self += py::self)
      .def(py::self += Variable())
      .def(py::self += double())
      // Subtraction.
      .def(py::self - py::self)
      .def(py::self - Variable())
      .def(py::self - double())
      .def(Variable() - py::self)
      .def(double() - py::self)
      .def(py::self -= py::self)
      .def(py::self -= Variable())
      .def(py::self -= double())
      // Multiplication.
      .def(py::self * py::self)
      .def(py::self * Variable())
      .def(py::self * double())
      .def(Variable() * py::self)
      .def(double() * py::self)
      .def(py::self *= py::self)
      .def(py::self *= Variable())
      .def(py::self *= double())
      // Division.
      .def(py::self / py::self)
      .def(py::self / Variable())
      .def(py::self / double())
      .def(Variable() / py::self)
      .def(double() / py::self)
      .def(py::self /= py::self)
      .def(py::self /= Variable())
      .def(py::self /= double())
      // Pow.
      .def("__pow__", [](const Expression& self,
                         const Expression& other) { return pow(self, other); })
      // TODO(soonho): need to add this to drake-symbolic
      // Unary Plus.
      // .def(+py::self)
      // Unary Minus.
      .def(-py::self)
      // LT(<).
      //
      // Note that for `double < Expression` case, the reflected op ('>' in this
      // case) is called. For example, `1 < x * y` will return `x * y > 1`.
      .def(py::self < py::self)
      .def(py::self < Variable())
      .def(py::self < double())
      // LE(<=).
      .def(py::self <= py::self)
      .def(py::self <= Variable())
      .def(py::self <= double())
      // GT(>).
      .def(py::self > py::self)
      .def(py::self > Variable())
      .def(py::self > double())
      // GE(>=).
      .def(py::self >= py::self)
      .def(py::self >= Variable())
      .def(py::self >= double())
      // EQ(==).
      .def(py::self == py::self)
      .def(py::self == Variable())
      .def(py::self == double())
      // NE(!=)
      .def(py::self != py::self)
      .def(py::self != Variable())
      .def(py::self != double())
      .def("Differentiate", &Expression::Differentiate)
      .def("ToPrefix", [](const Expression& self) { return ToPrefix(self); });

  m.def("log", py::overload_cast<const Expression&>(&log))
      .def("abs", &abs)
      .def("exp", &exp)
      .def("sqrt", &sqrt)
      .def("pow", py::overload_cast<const Expression&, const Expression&>(&pow))
      .def("sin", &sin)
      .def("cos", &cos)
      .def("tan", &tan)
      .def("asin", &asin)
      .def("acos", &acos)
      .def("atan", &atan)
      .def("atan2", &atan2)
      .def("sinh", &sinh)
      .def("cosh", &cosh)
      .def("tanh", &tanh)
      .def("min", &min)
      .def("max", &max);

  m.def("if_then_else", &if_then_else)
      .def("if_then_else",
           [](const Variable& v, const Expression& e_then,
              const Expression& e_else) {
             if (v.get_type() != Variable::Type::BOOLEAN) {
               throw std::runtime_error(
                   v.get_name() +
                   " is not a Boolean variable but used as a "
                   "conditional in if-then-else(" +
                   v.get_name() + ", " + e_then.to_string() + ", " +
                   e_else.to_string() + ")");
             }
             return if_then_else(Formula(v), e_then, e_else);
           })
      .def("if_then_else",
           [](const Formula& f, const Formula& f1, const Formula& f2) {
             return imply(f, f1) && imply(!f, f2);
           });

  m.def("forall",
        [](const std::vector<Variable>& vec, const Formula& f) {
          Variables vars;
          vars.insert(vec.begin(), vec.end());
          return forall(vars, f);
        })
      .def("forall", &forall);

  py::class_<Formula>(m, "Formula")
      .def("GetFreeVariables", &Formula::GetFreeVariables)
      .def("EqualTo", &Formula::EqualTo)
      .def("Evaluate", [](const Formula& self) { return self.Evaluate(); })
      .def("Evaluate",
           [](const Formula& self, const Environment::map& env) {
             Environment e;
             return self.Evaluate(Environment{env});
           })
      .def("Substitute",
           [](const Formula& self, const Variable& var, const Expression& e) {
             return self.Substitute(var, e);
           })
      .def("Substitute",
           [](const Formula& self, const ExpressionSubstitution& s) {
             return self.Substitute(s);
           })
      .def("to_string", &Formula::to_string)
      .def("__str__", &Formula::to_string)
      .def("__repr__",
           [](const Formula& self) {
             return fmt::format("<Formula \"{}\">", self.to_string());
           })
      .def("__eq__", [](const Formula& self,
                        const Formula& other) { return self.EqualTo(other); })
      .def("__ne__", [](const Formula& self,
                        const Formula& other) { return !self.EqualTo(other); })
      .def("__hash__",
           [](const Formula& self) { return std::hash<Formula>{}(self); })
      .def("__nonzero__", [](const Formula& f) { return f.Evaluate(); })
      // EQ(==).
      .def(py::self == Variable())
      // NEQ(!=).
      .def(py::self != Variable())
      .def_static("TRUE", &Formula::True)
      .def_static("FALSE", &Formula::False)
      .def("ToPrefix", [](const Formula& self) { return ToPrefix(self); });

  // __logical_and and __logical_or will be extended as `And` and `Or`
  // in `__init__.py` to accept an arbitrary number of arguments.
  m.def("__logical_and",
        [](const Formula& a, const Formula& b) { return a && b; })
      .def("__logical_or",
           [](const Formula& a, const Formula& b) { return a || b; });

  m.def("logical_not", [](const Formula& a) { return !a; })
      .def("logical_imply",
           [](const Formula& a, const Formula& b) { return imply(a, b); })
      .def("logical_iff",
           [](const Variable& a, const Variable& b) { return iff(a, b); })
      .def("logical_iff",
           [](const Formula& a, const Variable& b) { return iff(a, b); })
      .def("logical_iff",
           [](const Variable& a, const Formula& b) { return iff(a, b); })
      .def("logical_iff",
           [](const Formula& a, const Formula& b) { return iff(a, b); });

  py::implicitly_convertible<int, Expression>();
  py::implicitly_convertible<double, Expression>();
  py::implicitly_convertible<Variable, Expression>();

  py::class_<Config>(m, "Config")
      .def(py::init<>())
      .def_property("precision", &Config::precision,
                    [](Config& self, const double prec) {
                      self.mutable_precision() = prec;
                    })
      .def_property("use_polytope", &Config::use_polytope,
                    [](Config& self, const bool use_polytope) {
                      self.mutable_use_polytope() = use_polytope;
                    })
      .def_property("use_polytope_in_forall", &Config::use_polytope_in_forall,
                    [](Config& self, const bool use_polytope_in_forall) {
                      self.mutable_use_polytope_in_forall() =
                          use_polytope_in_forall;
                    })
      .def_property("use_worklist_fixpoint", &Config::use_worklist_fixpoint,
                    [](Config& self, const bool use_worklist_fixpoint) {
                      self.mutable_use_worklist_fixpoint() =
                          use_worklist_fixpoint;
                    })
      .def_property("use_local_optimization", &Config::use_local_optimization,
                    [](Config& self, const bool use_local_optimization) {
                      self.mutable_use_local_optimization() =
                          use_local_optimization;
                    })
      .def_property("nlopt_ftol_rel", &Config::nlopt_ftol_rel,
                    [](Config& self, const bool nlopt_ftol_rel) {
                      self.mutable_nlopt_ftol_rel() = nlopt_ftol_rel;
                    })
      .def_property("nlopt_ftol_abs", &Config::nlopt_ftol_abs,
                    [](Config& self, const bool nlopt_ftol_abs) {
                      self.mutable_nlopt_ftol_abs() = nlopt_ftol_abs;
                    })
      .def_property("nlopt_maxeval", &Config::nlopt_maxeval,
                    [](Config& self, const bool nlopt_maxeval) {
                      self.mutable_nlopt_maxeval() = nlopt_maxeval;
                    })
      .def_property("nlopt_maxtime", &Config::nlopt_maxtime,
                    [](Config& self, const bool nlopt_maxtime) {
                      self.mutable_nlopt_maxtime() = nlopt_maxtime;
                    })
      .def("__str__",
           [](const Config& self) { return fmt::format("{}", self); });

  py::enum_<Logic>(m, "Logic")
      .value("QF_NRA", Logic::QF_NRA)
      .value("QF_NRA_ODE", Logic::QF_NRA_ODE)
      .value("QF_LRA", Logic::QF_LRA)
      .value("QF_RDL", Logic::QF_RDL);

  py::class_<Context>(m, "Context")
      .def(py::init<>())
      .def("Assert", &Context::Assert)
      .def("CheckSat", &Context::CheckSat)
      .def("DeclareVariable",
           [](Context& self, const Variable& v) {
             return self.DeclareVariable(v);
           })
      .def("DeclareVariable",
           [](Context& self, const Variable& v, const Expression& lb,
              const Expression& ub) { return self.DeclareVariable(v, lb, ub); })
      .def("Exit", &Context::Exit)
      .def("Minimize",
           [](Context& self, const Expression& f) { return self.Minimize(f); })
      .def("Maximize",
           [](Context& self, const Expression& f) { return self.Maximize(f); })
      .def("Pop", &Context::Pop)
      .def("Push", &Context::Push)
      .def("SetInfo",
           py::overload_cast<const std::string&, double>(&Context::SetInfo))
      .def("SetInfo", py::overload_cast<const std::string&, const std::string&>(
                          &Context::SetInfo))
      .def("SetInterval", &Context::SetInterval)
      .def("SetLogic", &Context::SetLogic)
      .def("SetOption",
           py::overload_cast<const std::string&, double>(&Context::SetOption))
      .def("SetOption",
           py::overload_cast<const std::string&, const std::string&>(
               &Context::SetOption))
      .def_property("config", [](const Context& self) { return self.config(); },
                    [](Context& self, const Config& config) {
                      self.mutable_config() = config;
                    })
      .def_property_readonly_static(
          "version", [](py::object /* self */) { return Context::version(); })
      .def_property_readonly("box", &Context::box);

  m.def("CheckSatisfiability",
        py::overload_cast<const Formula&, double>(&CheckSatisfiability))
      .def("CheckSatisfiability",
           py::overload_cast<const Formula&, Config>(&CheckSatisfiability))
      .def(
          "CheckSatisfiability",
          py::overload_cast<const Formula&, double, Box*>(&CheckSatisfiability))
      .def(
          "CheckSatisfiability",
          py::overload_cast<const Formula&, Config, Box*>(&CheckSatisfiability))
      .def("Minimize",
           py::overload_cast<const Expression&, const Formula&, double>(
               &Minimize))
      .def("Minimize",
           py::overload_cast<const Expression&, const Formula&, Config>(
               &Minimize))
      .def("Minimize",
           py::overload_cast<const Expression&, const Formula&, double, Box*>(
               &Minimize))
      .def("Minimize",
           py::overload_cast<const Expression&, const Formula&, Config, Box*>(
               &Minimize));

  // Exposes spdlog::level::level_enum.
  py::enum_<spdlog::level::level_enum>(m, "LogLevel")
      .value("TRACE", spdlog::level::trace)
      .value("DEBUG", spdlog::level::debug)
      .value("WARNING", spdlog::level::warn)
      .value("ERROR", spdlog::level::err)
      .value("CRITICAL", spdlog::level::critical)
      .value("OFF", spdlog::level::off);

  m.def("set_log_level",
        [](const spdlog::level::level_enum l) { log()->set_level(l); });

  // NOLINTNEXTLINE(readability/fn_size)
}

}  // namespace dreal

#if defined __clang__
#if __has_warning("-Wself-assign-overloaded")
#pragma clang diagnostic pop
#endif
#endif
