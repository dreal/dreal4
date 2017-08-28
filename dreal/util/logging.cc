#include "dreal/util/logging.h"

#include <memory>
#include <string>

namespace dreal {

using std::shared_ptr;
using std::string;

shared_ptr<spdlog::logger> CreateLogger(const string& logger_name) {
  // Checks if there exists a logger with the name. If it exists, return it.
  const shared_ptr<spdlog::logger> logger{spdlog::get(logger_name)};
  if (logger) {
    return logger;
  }

  // Set format.
  spdlog::set_pattern("[%l] [%Y%m%d %H:%M:%S.%f] %v");

  // Create and return a new logger.
  return spdlog::stderr_color_mt(logger_name);
}

spdlog::logger* log() {
  static const shared_ptr<spdlog::logger> logger(CreateLogger("dreal_logger"));
  return logger.get();
}
}  // namespace dreal
