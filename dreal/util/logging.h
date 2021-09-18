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

}  // namespace dreal

#define DREAL_LOG_TRACE(...)                                \
  do {                                                      \
    if (::dreal::log()->should_log(spdlog::level::trace)) { \
      ::dreal::log()->trace(__VA_ARGS__);                   \
    }                                                       \
  } while (0)

#define DREAL_LOG_DEBUG(...)                                \
  do {                                                      \
    if (::dreal::log()->should_log(spdlog::level::debug)) { \
      ::dreal::log()->debug(__VA_ARGS__);                   \
    }                                                       \
  } while (0)

#define DREAL_LOG_INFO(...)            \
  do {                                 \
    ::dreal::log()->info(__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_WARN(...)            \
  do {                                 \
    ::dreal::log()->warn(__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_ERROR(...)            \
  do {                                  \
    ::dreal::log()->error(__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_CRITICAL(...)            \
  do {                                     \
    ::dreal::log()->critical(__VA_ARGS__); \
  } while (0)

#define DREAL_LOG_TRACE_ENABLED \
  (::dreal::log()->should_log(spdlog::level::trace))
#define DREAL_LOG_DEBUG_ENABLED \
  (::dreal::log()->should_log(spdlog::level::debug))
#define DREAL_LOG_INFO_ENABLED (::dreal::log()->should_log(spdlog::level::info))
#define DREAL_LOG_WARN_ENABLED (::dreal::log()->should_log(spdlog::level::warn))
#define DREAL_LOG_ERROR_ENABLED (::dreal::log()->should_log(spdlog::level::err))
#define DREAL_LOG_CRITICAL_ENABLED \
  (::dreal::log()->should_log(spdlog::level::critical))
