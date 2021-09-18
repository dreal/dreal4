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
#include "dreal/smt2/command.h"

#include <ostream>
#include <string>

#include "dreal/smt2/command_cell.h"
#include "dreal/smt2/logic.h"

namespace dreal {
using std::make_shared;
using std::ostream;
using std::string;

ostream& operator<<(ostream& os, const Command& c) {
  return c.ptr_->Display(os);
}

Command assert_command(const Formula& f) {
  return Command{make_shared<AssertCommand>(f)};
}

Command check_sat_command() { return Command{make_shared<CheckSatCommand>()}; }

Command exit_command() { return Command{make_shared<ExitCommand>()}; }

Command set_info_command(const string& key, const string& val) {
  return Command{make_shared<SetInfoCommand>(key, val)};
}

Command set_logic_command(Logic logic) {
  return Command{make_shared<SetLogicCommand>(logic)};
}

Command set_option_command(const string& key, const string& val) {
  return Command{make_shared<SetOptionCommand>(key, val)};
}

Command push_command(int level) {
  return Command{make_shared<PushCommand>(level)};
}

Command pop_command(int level) {
  return Command{make_shared<PopCommand>(level)};
}

Command reset_command() { return Command{make_shared<ResetCommand>()}; }

}  // namespace dreal
