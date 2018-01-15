#pragma once

#include <ostream>
#include <string>
#include <utility>

#include "dreal/smt2/command.h"
#include "dreal/symbolic/symbolic.h"

namespace dreal {

/// CommandCell class. It is the abstract base class of the classes
/// representing smt2lib commands.
class CommandCell {
 public:
  /// Default constructor.
  CommandCell() = default;

  /// Deleted copy-constructor.
  CommandCell(const CommandCell&) = delete;

  /// Deleted move-constructor.
  CommandCell(CommandCell&&) = default;

  /// Deleted copy-assignment operator.
  CommandCell& operator=(const CommandCell&) = delete;

  /// Deleted move-assignment operator.
  CommandCell& operator=(CommandCell&&) = delete;

  /// Default destructor.
  virtual ~CommandCell() = default;
  /// Output its string representation to @p os.
  virtual std::ostream& Display(std::ostream& os) const = 0;
};

/// "assert" command.
class AssertCommand : public CommandCell {
 public:
  explicit AssertCommand(Formula f) : f_{std::move(f)} {};
  const Formula& get_assertion() const { return f_; }
  std::ostream& Display(std::ostream& os) const override;

 private:
  const Formula f_;
};

/// "check-sat" command.
class CheckSatCommand : public CommandCell {
 public:
  CheckSatCommand() = default;
  std::ostream& Display(std::ostream& os) const override;
};

/// "echo" command.
class EchoCommand : public CommandCell {
 public:
  explicit EchoCommand(std::string message) : message_{std::move(message)} {}
  const std::string get_message() const { return message_; }
  std::ostream& Display(std::ostream& os) const override;

 private:
  const std::string message_;
};

/// "exit" command.
class ExitCommand : public CommandCell {
 public:
  ExitCommand() = default;
  std::ostream& Display(std::ostream& os) const override;
};

/// "get-assertions" command.
class GetAssertionsCommand : public CommandCell {
 public:
  GetAssertionsCommand() = default;
  std::ostream& Display(std::ostream& os) const override;
};

/// "get-assignments" command.
class GetAssignmentCommand : public CommandCell {
 public:
  GetAssignmentCommand() = default;
  std::ostream& Display(std::ostream& os) const override;
};

/// "get-info" command.
class GetInfoCommand : public CommandCell {
 public:
  GetInfoCommand() = default;
  const std::string get_key() const { return key_; }
  std::ostream& Display(std::ostream& os) const override;

 private:
  const std::string key_;
};

/// "get-model" command.
class GetModelCommand : public CommandCell {
 public:
  GetModelCommand() = default;
  std::ostream& Display(std::ostream& os) const override;
};

/// "get-option" command.
class GetOptionCommand : public CommandCell {
 public:
  explicit GetOptionCommand(std::string key) : key_{std::move(key)} {}
  const std::string get_key() const { return key_; }
  std::ostream& Display(std::ostream& os) const override;

 private:
  const std::string key_;
};

/// "get-proof" command.
class GetProofCommand : public CommandCell {
 public:
  GetProofCommand() = default;
  std::ostream& Display(std::ostream& os) const override;
};

/// "get-unsat-assumptions" command.
class GetUnsatAssumptionsCommand : public CommandCell {
 public:
  GetUnsatAssumptionsCommand() = default;
  std::ostream& Display(std::ostream& os) const override;
};

/// "get-unsat-core" command.
class GetUnsatCoreCommand : public CommandCell {
 public:
  GetUnsatCoreCommand() = default;
  std::ostream& Display(std::ostream& os) const override;
};

/// "pop" command.
class PopCommand : public CommandCell {
 public:
  explicit PopCommand(int level) : level_(level) {}
  int get_level() const { return level_; }
  std::ostream& Display(std::ostream& os) const override;

 private:
  const int level_{};
};

/// "push" command.
class PushCommand : public CommandCell {
 public:
  explicit PushCommand(int level) : level_(level) {}
  int get_level() const { return level_; }
  std::ostream& Display(std::ostream& os) const override;

 private:
  const int level_{};
};

/// "reset" command.
class ResetCommand : public CommandCell {
 public:
  ResetCommand() = default;
  std::ostream& Display(std::ostream& os) const override;
};

/// "reset-assertions" command.
class ResetAssertionsCommand : public CommandCell {
 public:
  ResetAssertionsCommand() = default;
  std::ostream& Display(std::ostream& os) const override;
};

/// "set-info" command.
class SetInfoCommand : public CommandCell {
 public:
  SetInfoCommand(std::string key, std::string value)
      : key_{std::move(key)}, value_{std::move(value)} {}
  const std::string& get_key() const { return key_; }
  const std::string& get_value() const { return value_; }
  std::ostream& Display(std::ostream& os) const override;

 private:
  const std::string key_;
  const std::string value_;
};

class SetLogicCommand : public CommandCell {
 public:
  explicit SetLogicCommand(const Logic logic) : logic_{logic} {}
  Logic get_logic() const { return logic_; }
  std::ostream& Display(std::ostream& os) const override;

 private:
  const Logic logic_;
};

class SetOptionCommand : public CommandCell {
 public:
  SetOptionCommand(std::string key, std::string value)
      : key_{std::move(key)}, value_{std::move(value)} {}
  std::ostream& Display(std::ostream& os) const override;

 private:
  const std::string key_;
  const std::string value_;
};

// TODO(soonho): Add support the following cases:
// class CheckSatAssumingCommand : public CommandCell {};
// class DeclareConstCommand : public CommandCell {};
// class DeclareFunCommand : public CommandCell {};
// class DeclareSortCommand : public CommandCell {};
// class DefineFunCommand : public CommandCell {};
// class DefineFunRecCommand : public CommandCell {};
// class DefineFunsRecCommand : public CommandCell {};
// class DefineSortCommand : public CommandCell {};
// class GetValueCommand : public CommandCell { };

}  // namespace dreal
