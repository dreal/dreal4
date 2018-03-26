#include "dreal/api/api.h"

#include <experimental/optional>

#include "pybind11/pybind11.h"
#include "pybind11/stl.h"

#include "dreal/util/box.h"

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

PYBIND11_MODULE(_api_py, m) {
  m.doc() = "dReal Python APIs";

  m.def("CheckSatisfiability",
        py::overload_cast<const Formula&, double>(&CheckSatisfiability));

  // TODO(soonho): Enable this.
  // m.def("CheckSatisfiability",
  //       py::overload_cast<const Formula&, Config>(&CheckSatisfiability));

  m.def("CheckSatisfiability",
        py::overload_cast<const Formula&, double, Box*>(&CheckSatisfiability));

  // TODO(soonho): Enable this.
  // m.def("CheckSatisfiability",
  //       py::overload_cast<const Formula&, Config,
  //       Box*>(&CheckSatisfiability));

  m.def(
      "Minimize",
      py::overload_cast<const Expression&, const Formula&, double>(&Minimize));

  // TODO(soonho): Enable this.
  // m.def(
  //     "Minimize",
  //     py::overload_cast<const Expression&, const Formula&,
  //     Config>(&Minimize));

  m.def("Minimize",
        py::overload_cast<const Expression&, const Formula&, double, Box*>(
            &Minimize));

  // TODO(soonho): Enable this.
  // m.def("Minimize",
  //       py::overload_cast<const Expression&, const Formula&, Config, Box*>(
  //           &Minimize));
}
}  // namespace dreal
