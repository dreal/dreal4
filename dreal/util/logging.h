#pragma once

#include "fmt/ostream.h"
#include "spdlog/spdlog.h"

namespace dreal {

/// Provide a global logger. See the following usage:
///
/// <pre>
/// DREAL_LOG_TRACE("message with param {0}, {1}", arg1, arg2);
/// DREAL_LOG_DEBUG("message with param {0}, {1}", arg1, arg2);
/// DREAL_LOG_INFO("Support for int: {0:d}; hex: {0:x};", 42, 32);
/// DREAL_LOG_WARN("Support for floats {:03.2f}", 1.23456);
/// DREAL_LOG_ERROR("Positional args are {1} {0}..", "too", "supported");
/// DREAL_LOG_CRITICAL("{:<30}", "left aligned");
/// </pre>
///
/// Please check https://github.com/gabime/spdlog for more information.
spdlog::logger* log();

#define DREAL_LOG_TRACE(...)                       \
  do {                                             \
    if (log()->should_log(spdlog::level::trace)) { \
      log()->trace(__VA_ARGS__);                   \
    }                                              \
  } while (0)

#define DREAL_LOG_DEBUG(...)                       \
  do {                                             \
    if (log()->should_log(spdlog::level::debug)) { \
      log()->debug(__VA_ARGS__);                   \
    }                                              \
  } while (0)

#define DREAL_LOG_INFO(...)   \
  do {                        \
    log()->info(__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_WARN(...)   \
  do {                        \
    log()->warn(__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_ERROR(...)   \
  do {                         \
    log()->error(__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_CRITICAL(...)   \
  do {                            \
    log()->critical(__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_TRACE_ENABLED (log()->should_log(spdlog::level::trace))
#define DREAL_LOG_DEBUG_ENABLED (log()->should_log(spdlog::level::debug))
#define DREAL_LOG_INFO_ENABLED (log()->should_log(spdlog::level::info))
#define DREAL_LOG_WARN_ENABLED (log()->should_log(spdlog::level::warn))
#define DREAL_LOG_ERROR_ENABLED (log()->should_log(spdlog::level::err))
#define DREAL_LOG_CRITICAL_ENABLED (log()->should_log(spdlog::level::critical))

}  // namespace dreal
