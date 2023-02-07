/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "./ibex.h"
#include "fmt/format.h"
#include "fmt/ostream.h"
#include "pybind11/functional.h"
#include "pybind11/operators.h"
#include "pybind11/pybind11.h"
#include "pybind11/stl.h"

#include "dreal/api/api.h"
#include "dreal/contractor/contractor_status.h"
#include "dreal/smt2/logic.h"
#include "dreal/solver/config.h"
#include "dreal/solver/context.h"
#include "dreal/solver/theory_solver.h"
#include "dreal/symbolic/prefix_printer.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/dynamic_bitset.h"
#include "dreal/util/if_then_else_eliminator.h"
#include "dreal/util/interrupt.h"
#include "dreal/util/logging.h"
#include "dreal/util/optional.h"
#include "dreal/util/signal_handler_guard.h"

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

namespace {
void sigint_handler(int) { g_interrupted = true; }

struct IbexBitSetIterator {
  IbexBitSetIterator(const ibex::BitSet& bitset, py::object ref)
      : it_{bitset.begin()}, end_{bitset.end()}, ref_{ref} {}

  int next() {
    if (it_ == end_) {
      throw py::stop_iteration();
    }
    return (it_++).el;
  }

 private:
  ibex::BitSet::iterator it_;
  const ibex::BitSet::iterator end_;
  py::object ref_;  // keep a reference
};

}  // namespace

PYBIND11_MODULE(_dreal_py, m) {
  m.doc() = "dReal Python Module";

  py::class_<IbexBitSetIterator>(m, "ibex::BitSet::iterator")
      .def("__iter__",
           [](IbexBitSetIterator& it) -> IbexBitSetIterator& { return it; })
      .def("__next__", &IbexBitSetIterator::next);

  py::class_<ibex::BitSet>(m, "Bitset")
      .def(py::init<>())
      .def(py::init<int>())
      .def(py::init<const ibex::BitSet&>())
      .def(py::init<const int, const int*>())
      .def("resize", &ibex::BitSet::resize)
      .def("compose", &ibex::BitSet::compose)
      .def("min", &ibex::BitSet::min)
      .def("max", &ibex::BitSet::max)
      .def("remove", &ibex::BitSet::remove)
      .def("next", &ibex::BitSet::next)
      .def("size", &ibex::BitSet::size)
      .def("add", &ibex::BitSet::add)
      .def("empty", [](const ibex::BitSet& self) { return self.empty(); })
      .def("fill", &ibex::BitSet::fill)
      .def("clear", &ibex::BitSet::clear)
      .def("__getitem__",
           [](const ibex::BitSet& self, const int idx) { return self[idx]; })
      .def("__iter__", [](py::object s) {
        return IbexBitSetIterator(s.cast<const ibex::BitSet&>(), s);
      });

  py::class_<Box::Interval>(m, "Interval")
      .def(py::init<>())
      .def(py::init<double, double>())
      .def(py::init<double>())
      .def("__abs__", [](const Box::Interval& self) { return abs(self); })
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
      // "Max" not "max" to avoid conflcits with python built-in function, max.
      .def("Max", [](const Box::Interval& i1,
                     const Box::Interval& i2) { return max(i1, i2); })
      // "Min" not "min" to avoid conflcits with python built-in function, min.
      .def("Min", [](const Box::Interval& i1,
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
           [](const Box&, const Variable&) {
             throw std::runtime_error{
                 "Box class does not allow deleting an item"};
           })
      .def("clear",
           [](const Box&) {
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
      .def("__str__", [](const Box& self) { return fmt::format("{}", self); })
      .def("set", [](Box& self, const Box& b) { return self = b; });

  py::class_<Variable> variable(m, "Variable");
  variable.def(py::init<const string&>())
      .def(py::init<const string&, Variable::Type>())
      .def("__abs__", [](const Variable& self) { return abs(self); })
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
      .def(
          "__pow__",
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
      .def(
          "__iter__",
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
      .def("__abs__", [](const Expression& self) { return abs(self); })
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
      // "Min" not "min" to avoid conflcits with python built-in function, min.
      .def("Min", &min)
      // "Max" not "max" to avoid conflcits with python built-in function, max.
      .def("Max", &max);

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

  // clang-format off
  m.def("forall", [](const std::vector<Variable>& vec, const Formula& f) {
    Variables vars;
    vars.insert(vec.begin(), vec.end());
    return forall(vars, f);
  }).def("forall", &forall);
  // clang-format on

  py::class_<Formula>(m, "Formula")
      .def(py::init<const Variable&>())
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
      .def("__logical_and",
           [](const Variable& a, const Formula& b) { return a && b; })
      .def("__logical_and",
           [](const Formula& a, const Variable& b) { return a && b; })
      .def("__logical_and",
           [](const Variable& a, const Variable& b) { return a && b; });

  m.def("__logical_or",
        [](const Formula& a, const Formula& b) { return a || b; })
      .def("__logical_or",
           [](const Variable& a, const Formula& b) { return a || b; })
      .def("__logical_or",
           [](const Formula& a, const Variable& b) { return a || b; })
      .def("__logical_or",
           [](const Variable& a, const Variable& b) { return a || b; });

  // clang-format off
  m.def("logical_not", [](const Formula& a) {
    return !a;
  }).def("logical_not", [](const Variable& a) { return !a; });
  // clang-format on

  m.def("logical_imply",
        [](const Formula& a, const Formula& b) { return imply(a, b); })
      .def("logical_imply",
           [](const Variable& a, const Formula& b) { return imply(a, b); })
      .def("logical_imply",
           [](const Formula& a, const Variable& b) { return imply(a, b); })
      .def("logical_imply",
           [](const Variable& a, const Variable& b) { return imply(a, b); });

  m.def("logical_iff",
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
      .def_property("number_of_jobs", &Config::number_of_jobs,
                    [](Config& self, const int number_of_jobs) {
                      self.mutable_number_of_jobs() = number_of_jobs;
                    })
      .def_property("brancher", &Config::brancher,
                    [](Config& self, const Config::Brancher& brancher) {
                      self.mutable_brancher() = brancher;
                    })
      .def("__str__",
           [](const Config& self) { return fmt::format("{}", self); });

  py::enum_<Logic>(m, "Logic")
      .value("ALL", Logic::ALL)
      .value("QF_LIA", Logic::QF_LIA)
      .value("QF_LIRA", Logic::QF_LIRA)
      .value("QF_LRA", Logic::QF_LRA)
      .value("QF_NIA", Logic::QF_NIA)
      .value("QF_NIAT", Logic::QF_NIAT)
      .value("QF_NIRA", Logic::QF_NIRA)
      .value("QF_NIRAT", Logic::QF_NIRAT)
      .value("QF_NRA", Logic::QF_NRA)
      .value("QF_NRAT", Logic::QF_NRAT)
      .value("QF_RDL", Logic::QF_RDL);

  py::class_<Context>(m, "Context")
      .def(py::init<>())
      .def("Assert", &Context::Assert)
      .def("CheckSat",
           [](Context& self) {
             SignalHandlerGuard guard{SIGINT, &sigint_handler, &g_interrupted};
             return self.CheckSat();
           })
      .def("DeclareVariable",
           [](Context& self, const Variable& v) {
             return self.DeclareVariable(v);
           })
      .def("DeclareVariable",
           [](Context& self, const Variable& v, const Expression& lb,
              const Expression& ub) { return self.DeclareVariable(v, lb, ub); })
      .def_static("Exit", &Context::Exit)
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
      .def_property("config", &Context::config,
                    [](Context& self, const Config& config) {
                      self.mutable_config() = config;
                    })
      .def_property_readonly_static(
          "version", [](py::object /* self */) { return Context::version(); })
      .def_property_readonly("box", &Context::box);

  m.def("CheckSatisfiability",
        [](const Formula& f, double delta) {
          SignalHandlerGuard guard{SIGINT, &sigint_handler, &g_interrupted};
          return CheckSatisfiability(f, delta);
        })
      .def("CheckSatisfiability",
           [](const Formula& f, Config config) {
             SignalHandlerGuard guard{SIGINT, &sigint_handler, &g_interrupted};
             return CheckSatisfiability(f, config);
           })
      .def("CheckSatisfiability",
           [](const Formula& f, double delta, Box* box) {
             SignalHandlerGuard guard{SIGINT, &sigint_handler, &g_interrupted};
             return CheckSatisfiability(f, delta, box);
           })
      .def("CheckSatisfiability",
           [](const Formula& f, Config config, Box* box) {
             SignalHandlerGuard guard{SIGINT, &sigint_handler, &g_interrupted};
             return CheckSatisfiability(f, config, box);
           })
      .def("Minimize",
           [](const Expression& objective, const Formula& constraint,
              const double delta) {
             SignalHandlerGuard guard{SIGINT, &sigint_handler, &g_interrupted};
             return Minimize(objective, constraint, delta);
           })
      .def("Minimize",
           [](const Expression& objective, const Formula& constraint,
              Config config) {
             SignalHandlerGuard guard{SIGINT, &sigint_handler, &g_interrupted};
             return Minimize(objective, constraint, config);
           })
      .def("Minimize",
           [](const Expression& objective, const Formula& constraint,
              const double delta, Box* const box) {
             SignalHandlerGuard guard{SIGINT, &sigint_handler, &g_interrupted};
             return Minimize(objective, constraint, delta, box);
           })
      .def("Minimize",
           [](const Expression& objective, const Formula& constraint,
              Config config, Box* const box) {
             SignalHandlerGuard guard{SIGINT, &sigint_handler, &g_interrupted};
             return Minimize(objective, constraint, config, box);
           });

  m.def("DeltaStrengthen", DeltaStrengthen);
  m.def("DeltaWeaken", DeltaWeaken);
  m.def("EliminateIfThenElse",
        [](const Formula& f) { return IfThenElseEliminator{}.Process(f); });

  // Exposes spdlog::level::level_enum.
  py::enum_<spdlog::level::level_enum>(m, "LogLevel")
      .value("TRACE", spdlog::level::trace)
      .value("DEBUG", spdlog::level::debug)
      .value("INFO", spdlog::level::info)
      .value("WARNING", spdlog::level::warn)
      .value("ERROR", spdlog::level::err)
      .value("CRITICAL", spdlog::level::critical)
      .value("OFF", spdlog::level::off);

  m.def("set_log_level",
        [](const spdlog::level::level_enum l) { log()->set_level(l); });

  m.def("BuildContractor", [](const std::vector<Formula>& assertions,
                              ContractorStatus* cs, const Config& config) {
    TheorySolver tsolver{config};
    return *(tsolver.BuildContractor(assertions, cs));
  });

  py::class_<DynamicBitset>(m, "DynamicBitset")
      .def(
          py::init([](DynamicBitset::size_type n) { return DynamicBitset(n); }))
      // Note: The resulting string contains size() characters with
      // the first character corresponds to the last (size() - 1th)
      // bit and the last character corresponding to the first bit.
      .def("__str__",
           [](const DynamicBitset& self) { return fmt::format("{}", self); })

      .def("all", &DynamicBitset::all)
      .def("any", &DynamicBitset::any)
      .def("none", &DynamicBitset::none)

      .def("get",
           [](const DynamicBitset& self, int i) { return bool{self[i]}; })

      // Set all the bits of the sul::dynamic_bitset to false.
      .def("reset", py::overload_cast<>(&DynamicBitset::reset))
      .def("size", &DynamicBitset::size)
      // Set all the bits of the sul::dynamic_bitset to true.
      .def("set", py::overload_cast<>(&DynamicBitset::set))
      .def("set", py::overload_cast<DynamicBitset::size_type, bool>(
                      &DynamicBitset::set))
      // Test if two DynamicBitset have the same content.
      .def("__eq__", [](const DynamicBitset& self,
                        const DynamicBitset& other) { return self == other; })
      // Test if two DynamicBitset do have the same content.
      .def("__ne__", [](const DynamicBitset& self,
                        const DynamicBitset& other) { return self != other; })

      // Performs binary AND on corresponding pairs of bits of self and other.
      .def("__and__", [](const DynamicBitset& self,
                         const DynamicBitset& other) { return self & other; })
      // Sets the bits to the result of binary AND on corresponding pairs of
      // bits of self and other
      .def("__iand__", [](DynamicBitset& self,
                          const DynamicBitset& other) { return self &= other; })
      // Performs binary OR on corresponding pairs of bits of self and other.
      .def("__or__", [](const DynamicBitset& self,
                        const DynamicBitset& other) { return self | other; })
      // Sets the bits to the result of binary OR on corresponding pairs of
      // bits of self and other.
      .def("__ior__", [](DynamicBitset& self, const DynamicBitset& other) {
        return self |= other;
      });

  py::class_<ContractorStatus>(m, "ContractorStatus")
      .def(py::init<Box>())
      .def("box",
           [](const ContractorStatus& self) {
             // Explicitly create a copy.
             //
             // TODO(soonho): Impose constness here and remove this redundant
             // copy.
             return Box(self.box());
           })
      .def("mutable_box", &ContractorStatus::mutable_box,
           py::return_value_policy::reference_internal)
      .def("output",
           [](const ContractorStatus& self) {
             // Explicitly create a copy.
             //
             // TODO(soonho): Impose constness here and remove this redundant
             // copy.
             return DynamicBitset(self.output());
           })
      .def("mutable_output", &ContractorStatus::mutable_output,
           py::return_value_policy::reference_internal)
      .def("explanation", &ContractorStatus::Explanation);

  py::class_<Contractor>(m, "Contractor")
      .def(py::init<const Config&>())
      .def("__str__",
           [](const Contractor& self) { return fmt::format("{}", self); })
      .def("Prune", &Contractor::Prune)
      .def("input", [](const Contractor& self) {
        // Explicitly create a copy.
        //
        // TODO(soonho): Impose constness here and remove this redundant
        // copy.
        return DynamicBitset(self.input());
      });

  // NOLINTNEXTLINE(readability/fn_size)
}

}  // namespace dreal

#if defined __clang__
#if __has_warning("-Wself-assign-overloaded")
#pragma clang diagnostic pop
#endif
#endif
