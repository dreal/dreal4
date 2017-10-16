#pragma once

#ifndef NDEBUG
#define SPDLOG_DEBUG_ON 1
#define SPDLOG_TRACE_ON 1
#endif

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

#ifndef NDEBUG
#define DREAL_LOG_TRACE(fmt, ...)            \
  do {                                       \
    SPDLOG_TRACE(log(), fmt, ##__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_DEBUG(fmt, ...)            \
  do {                                       \
    SPDLOG_DEBUG(log(), fmt, ##__VA_ARGS__); \
  } while (0)
#else
#define DREAL_LOG_TRACE(fmt, ...)     \
  do {                                \
    log()->trace(fmt, ##__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_DEBUG(fmt, ...)     \
  do {                                \
    log()->debug(fmt, ##__VA_ARGS__); \
  } while (0)
#endif

#define DREAL_LOG_INFO(fmt, ...)     \
  do {                               \
    log()->info(fmt, ##__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_WARN(fmt, ...)     \
  do {                               \
    log()->warn(fmt, ##__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_ERROR(fmt, ...)     \
  do {                                \
    log()->error(fmt, ##__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_CRITICAL(fmt, ...)     \
  do {                                   \
    log()->critical(fmt, ##__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_TRACE_ENABLED (log()->should_log(spdlog::level::trace))
#define DREAL_LOG_DEBUG_ENABLED (log()->should_log(spdlog::level::debug))
#define DREAL_LOG_INFO_ENABLED (log()->should_log(spdlog::level::info))
#define DREAL_LOG_WARN_ENABLED (log()->should_log(spdlog::level::warn))
#define DREAL_LOG_ERROR_ENABLED (log()->should_log(spdlog::level::error))
#define DREAL_LOG_CRITICAL_ENABLED (log()->should_log(spdlog::level::critical))

}  // namespace dreal
