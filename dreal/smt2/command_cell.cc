#include "dreal/smt2/command_cell.h"

namespace dreal {

// -------------
// AssertCommand
// -------------
std::ostream& AssertCommand::Display(std::ostream& os) const {
  return os << "(assert " << f_ << ")";
}

// -------------
// CheckSatCommand
// -------------
std::ostream& CheckSatCommand::Display(std::ostream& os) const {
  return os << "(check-sat)";
}

// -------------
// EchoCommand
// -------------
std::ostream& EchoCommand::Display(std::ostream& os) const {
  return os << "(echo " << message_ << ")";
}

// -------------
// ExitCommand
// -------------
std::ostream& ExitCommand::Display(std::ostream& os) const {
  return os << "(exit)";
}

// --------------------
// GetAssertionsCommand
// --------------------
std::ostream& GetAssertionsCommand::Display(std::ostream& os) const {
  return os << "(get-assertions)";
}

// --------------
// GetInfoCommand
// --------------
std::ostream& GetInfoCommand::Display(std::ostream& os) const {
  return os << "(get-info " << key_ << ")";
}

// --------------
// GetModelCommand
// --------------
std::ostream& GetModelCommand::Display(std::ostream& os) const {
  return os << "(get-model)";
}

// ----------------
// GetOptionCommand
// ----------------
std::ostream& GetOptionCommand::Display(std::ostream& os) const {
  return os << "(get-option " << key_ << ")";
}

// ---------------
// GetProofCommand
// ---------------
std::ostream& GetProofCommand::Display(std::ostream& os) const {
  return os << "(get-proof)";
}

// --------------------------
// GetUnsatAssumptionsCommand
// --------------------------
std::ostream& GetUnsatAssumptionsCommand::Display(std::ostream& os) const {
  return os << "(get-unsat-assumptions)";
}

// --------------------------
// GetUnsatCoreCommand
// --------------------------
std::ostream& GetUnsatCoreCommand::Display(std::ostream& os) const {
  return os << "(get-unsat-core)";
}

// ----------
// PopCommand
// ----------
std::ostream& PopCommand::Display(std::ostream& os) const {
  return os << "(pop " << level_ << ")";
}

// -----------
// PushCommand
// -----------
std::ostream& PushCommand::Display(std::ostream& os) const {
  return os << "(push " << level_ << ")";
}

// ------------
// ResetCommand
// ------------
std::ostream& ResetCommand::Display(std::ostream& os) const {
  return os << "(reset)";
}

// ----------------------
// ResetAssertionsCommand
// ----------------------
std::ostream& ResetAssertionsCommand::Display(std::ostream& os) const {
  return os << "(reset-assertions)";
}

// --------------
// SetInfoCommand
// --------------
std::ostream& SetInfoCommand::Display(std::ostream& os) const {
  return os << "(set-info " << key_ << " " << value_ << ")";
}

// ---------------
// SetLogicCommand
// ---------------
std::ostream& SetLogicCommand::Display(std::ostream& os) const {
  return os << "(set-logic " << logic_ << ")";
}

// ----------------
// SetOptionCommand
// ----------------
std::ostream& SetOptionCommand::Display(std::ostream& os) const {
  return os << "(set-option " << key_ << " " << value_ << ")";
}

}  // namespace dreal
