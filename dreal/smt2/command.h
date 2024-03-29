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

#include <memory>
#include <ostream>
#include <string>
#include <utility>

#include "dreal/smt2/logic.h"
#include "dreal/symbolic/symbolic.h"

namespace dreal {

class CommandCell;

/** Command class in smt2lib. It only includes a shared_ptr to
 * CommandCell.*/
class Command {
 public:
  explicit Command(std::shared_ptr<CommandCell> ptr) : ptr_{std::move(ptr)} {}

 private:
  std::shared_ptr<CommandCell> ptr_;

  friend std::ostream& operator<<(std::ostream& os, const Command& c);
};
std::ostream& operator<<(std::ostream& os, const Command& c);

Command assert_command(const Formula& f);
Command check_sat_command();
Command exit_command();
Command pop_command(int level);
Command push_command(int level);
Command reset_command();
Command set_info_command(const std::string& key, const std::string& val);
Command set_logic_command(Logic logic);
Command set_option_command(const std::string& key, const std::string& val);

}  // namespace dreal
