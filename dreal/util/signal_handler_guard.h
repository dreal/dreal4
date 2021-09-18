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

#include <atomic>
#include <csignal>

namespace dreal {

/// Sets a new signal handler and restores the old one when it goes
/// out of scope. When the flag is set, its destructor clears it out.
///
/// Motivation
/// ----------
///
/// Python's signal handler merely set a flag which is only checked in
/// the next python instruction. As a result, "C/C++ code may run
/// uninterrupted for an arbitrary amount of time" (from :
/// https://docs.python.org/3/library/signal.html#execution-of-python-signal-handlers)
///
/// Our approach
/// ------------
///
/// We provide a custom signal handler for SIGINT, which sets a global
/// flag (g_interrupted) which is monitored inside of dReal code. When
/// the flag is set, the checking code is supposed to throw an
/// exception, which will terminate the C++ call gracefully.  The C++
/// exception will be handled by pybind11, which will translate it to
/// a Python exception.
class SignalHandlerGuard {
 public:
  using handler_t = void (*)(int);

  /// Registers the new handler and saves the current one.
  SignalHandlerGuard(int sig, handler_t handler,
                     volatile std::atomic_bool* flag);
  SignalHandlerGuard(const SignalHandlerGuard&) = delete;
  SignalHandlerGuard(SignalHandlerGuard&&) = delete;
  SignalHandlerGuard& operator=(const SignalHandlerGuard&) = delete;
  SignalHandlerGuard& operator=(SignalHandlerGuard&&) = delete;

  /// Restores the old signal handler. If the flag is set, clear it.
  ~SignalHandlerGuard();

 private:
  const int sig_{0};
  volatile std::atomic_bool* flag_;

  using sigaction_t = struct sigaction;
  sigaction_t old_action_;
};
}  // namespace dreal
