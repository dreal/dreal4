#include <functional>
#include <string>

#include "fmt/format.h"
#include "fmt/ostream.h"
#include "pybind11/operators.h"
#include "pybind11/pybind11.h"
#include "pybind11/stl.h"

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/exception.h"

namespace dreal {

using std::string;

// NOLINTNEXTLINE(build/namespaces)
namespace py = pybind11;

PYBIND11_MODULE(_dreal_symbolic_py, m) {
  m.doc() = "Symbolic variable, variables, expression, and formula";

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
      .def("Differentiate", &Expression::Differentiate);

  m.def("log", &log)
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
               throw DREAL_RUNTIME_ERROR(
                   "{} is not a Boolean variable but used as a "
                   "conditional in if-then-else({}, {}, {})",
                   v, v, e_then, e_else);
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
      .def_static("TRUE", &Formula::True)
      .def_static("FALSE", &Formula::False);

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
           [](const Formula& a, const Formula& b) { return iff(a, b); });

  py::implicitly_convertible<int, Expression>();
  py::implicitly_convertible<double, Expression>();
  py::implicitly_convertible<Variable, Expression>();
}

}  // namespace dreal
