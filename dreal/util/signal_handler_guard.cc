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
#include "dreal/util/signal_handler_guard.h"

#include <iostream>
#include <stdexcept>

namespace dreal {

using std::runtime_error;

SignalHandlerGuard::SignalHandlerGuard(const int sig, handler_t handler,
                                       volatile std::atomic_bool* flag)
    : sig_{sig}, flag_{flag}, old_action_{} {
  // Register the new handler and save the current one.
  sigaction_t new_action{};
  new_action.sa_handler = handler;
  sigemptyset(&new_action.sa_mask);
  new_action.sa_flags = SA_RESTART;
  const int result = sigaction(sig_, &new_action, &old_action_);
  if (result != 0) {
    throw runtime_error("Failed to register the signal handler.");
  }
}

SignalHandlerGuard::~SignalHandlerGuard() {
  // Restore the old signal handler
  sigaction(sig_, &old_action_, nullptr);
  if (*flag_) {
    *(flag_) = false;
  }
}
}  // namespace dreal
