#include <experimental/optional>

#include "dreal/solver/config.h"
#include "dreal/solver/context.h"
#include "dreal/util/box.h"

#include "fmt/format.h"
#include "fmt/ostream.h"
#include "pybind11/pybind11.h"
#include "pybind11/stl.h"

namespace pybind11 {
namespace detail {
// Need this specialization to make optional<Box> working.
template <>
struct type_caster<std::experimental::optional<dreal::Box>>
    : public optional_caster<std::experimental::optional<dreal::Box>> {};
}  // namespace detail
}  // namespace pybind11

namespace dreal {

// NOLINTNEXTLINE(build/namespaces)
namespace py = pybind11;

PYBIND11_MODULE(_dreal_solver_py, m) {
  m.doc() = "Config and Context.";
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
      .def("Pop", &Context::Pop)    //
      .def("Push", &Context::Push)  //
      .def("SetInfo",
           py::overload_cast<const std::string&, double>(&Context::SetInfo))
      .def("SetInfo", py::overload_cast<const std::string&, const std::string&>(
                          &Context::SetInfo))
      .def("SetInterval", &Context::SetInterval)  //
      .def("SetLogic", &Context::SetLogic)        //
      .def("SetOption",
           py::overload_cast<const std::string&, double>(&Context::SetOption))
      .def("SetOption",
           py::overload_cast<const std::string&, const std::string&>(
               &Context::SetOption))
      .def_property("config", [](const Context& self) { return self.config(); },
                    [](Context& self, const Config& config) {
                      self.mutable_config() = config;
                    })
      .def_property_readonly_static(  //
          "version", [](py::object /* self */) { return Context::version(); })
      .def_property_readonly("box", &Context::box);
}

}  // namespace dreal
