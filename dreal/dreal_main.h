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

#include <iostream>
#include <string>
#include <vector>

// TODO(soonho): Fix ezoptionparser to remove those pragmas.
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wshadow"
#endif
#include "./ezOptionParser.hpp"
#ifdef __clang__
#pragma clang diagnostic pop
#endif
#pragma GCC diagnostic pop

#include "dreal/solver/config.h"

namespace dreal {

/// dReal's main program. It parses options from command line and
/// process a given file (either .smt2 or .dr file).
class MainProgram {
 public:
  /// Constructs a main program using given command-line arguments.
  MainProgram(int argc, const char* argv[]);
  /// Executes the main program.
  int Run();

 private:
  void PrintUsage();
  void AddOptions();
  bool ValidateOptions();

  // Extracts options from `opt_` and construts `config_`.
  void ExtractOptions();

  bool is_options_all_valid_{false};
  ez::ezOptionParser opt_;
  std::vector<const std::string*> args_;  // List of valid option arguments.
  Config config_;
};
}  // namespace dreal
