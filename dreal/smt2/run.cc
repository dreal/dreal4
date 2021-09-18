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
#include "dreal/smt2/run.h"

#include "dreal/smt2/driver.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::string;

void RunSmt2(const string& filename, const Config& config,
             const bool debug_scanning, const bool debug_parsing) {
  Smt2Driver smt2_driver{Context{config}};
  // Set up --debug-scanning option.
  smt2_driver.set_trace_scanning(debug_scanning);
  DREAL_LOG_DEBUG("RunSmt2() --debug-scanning = {}",
                  smt2_driver.trace_scanning());
  // Set up --debug-parsing option.
  smt2_driver.set_trace_parsing(debug_parsing);
  DREAL_LOG_DEBUG("RunSmt2() --debug-parsing = {}",
                  smt2_driver.trace_parsing());
  smt2_driver.parse_file(filename);
}
}  // namespace dreal
