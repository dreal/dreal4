#include <functional>
#include <string>
#include <utility>
#include <vector>

#include "fmt/format.h"
#include "fmt/ostream.h"
#include "pybind11/operators.h"
#include "pybind11/pybind11.h"
#include "pybind11/stl.h"

#include "dreal/util/box.h"

namespace dreal {

using std::pair;
using std::string;
using std::vector;

// NOLINTNEXTLINE(build/namespaces)
namespace py = pybind11;

PYBIND11_MODULE(_dreal_util_py, m) {
  m.doc() = "Interval and Box";

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
}

}  // namespace dreal
