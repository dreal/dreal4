#include "dreal/smt2/logic.h"

#include "pybind11/pybind11.h"
#include "pybind11/stl.h"

namespace dreal {

// NOLINTNEXTLINE(build/namespaces)
namespace py = pybind11;

PYBIND11_MODULE(_dreal_smt2_py, m) {
  m.doc() = "SMT2";

  py::enum_<Logic>(m, "Logic")
      .value("QF_NRA", Logic::QF_NRA)
      .value("QF_NRA_ODE", Logic::QF_NRA_ODE)
      .value("QF_LRA", Logic::QF_LRA)
      .value("QF_RDL", Logic::QF_RDL);
}

}  // namespace dreal
