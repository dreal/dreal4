#include "dreal/dr/run.h"

#include "dreal/dr/driver.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::string;

void RunDr(const string& filename, const Config& config,
           const bool debug_scanning, const bool debug_parsing) {
  DrDriver dr_driver{Context{config}};
  // Set up --debug-scanning option.
  dr_driver.trace_scanning_ = debug_scanning;
  DREAL_LOG_DEBUG("RunDr() --debug-scanning = {}", dr_driver.trace_scanning_);
  // Set up --debug-parsing option.
  dr_driver.trace_parsing_ = debug_parsing;
  DREAL_LOG_DEBUG("RunDr() --debug-parsing = {}", dr_driver.trace_parsing_);
  dr_driver.parse_file(filename);
}
}  // namespace dreal
