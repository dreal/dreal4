#pragma once

#include <atomic>

namespace dreal {
/// Flag to indicate an interrupt (SIGINT) is received.
extern volatile std::atomic_bool g_interrupted;
}  // namespace dreal
