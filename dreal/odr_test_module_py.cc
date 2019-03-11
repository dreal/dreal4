#include "pybind11/pybind11.h"

#include <string>

#include "dreal/symbolic/symbolic.h"

namespace dreal {

PYBIND11_MODULE(_odr_test_module_py, m) {
  m.doc() = "Test ODR using Variable.";
  m.def("new_variable", [](const std::string& name) { return Variable{name}; });
}

}  // namespace dreal
