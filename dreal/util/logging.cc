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
#include "dreal/util/logging.h"

#include <memory>
#include <string>

#include "spdlog/sinks/stdout_color_sinks.h"

namespace dreal {

using std::shared_ptr;
using std::string;

shared_ptr<spdlog::logger> CreateLogger(const string& logger_name) {
  // Checks if there exists a logger with the name. If it exists, return it.
  shared_ptr<spdlog::logger> logger{spdlog::get(logger_name)};
  if (logger) {
    return logger;
  }

  // Create and return a new logger.
  logger = spdlog::stderr_color_mt(logger_name);

  // Turn it off by default so that external programs using dReal as a library
  // do not see internal loggings.
  logger->set_level(spdlog::level::off);

  // Set format.
  logger->set_pattern("[%l] [%Y%m%d %H:%M:%S.%f] %v");

  return logger;
}

spdlog::logger* log() {
  static const shared_ptr<spdlog::logger> logger(CreateLogger("dreal_logger"));
  return logger.get();
}
}  // namespace dreal
