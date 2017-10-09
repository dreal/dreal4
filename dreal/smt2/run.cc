#include "dreal/smt2/run.h"

#include "dreal/smt2/driver.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::string;

void RunSmt2(const string& filename, const Config& config,
             const bool debug_scanning, const bool debug_parsing) {
  Smt2Driver smt2_driver{Context{config}};
  // Set up --debug-scanning option.
  smt2_driver.trace_scanning_ = debug_scanning;
  DREAL_LOG_DEBUG("RunSmt2() --debug-scanning = {}",
                  smt2_driver.trace_scanning_);
  // Set up --debug-parsing option.
  smt2_driver.trace_parsing_ = debug_parsing;
  DREAL_LOG_DEBUG("RunSmt2() --debug-parsing = {}", smt2_driver.trace_parsing_);
  smt2_driver.parse_file(filename);
}
}  // namespace dreal
