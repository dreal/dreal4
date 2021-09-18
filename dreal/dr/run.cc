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
