#include "dreal/solver/config.h"

#include "pybind11/pybind11.h"
#include "pybind11/stl.h"

namespace dreal {

// NOLINTNEXTLINE(build/namespaces)
namespace py = pybind11;

PYBIND11_MODULE(_solver_py, m) {
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
                    });
}
}  // namespace dreal
