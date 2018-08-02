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
