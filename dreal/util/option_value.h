#pragma once

#include <cassert>
#include <utility>

namespace dreal {

/// Represents an optional value in dReal. There are three ways that
/// an option can have its value -- by default, by command-line
/// argument, and by file (.smt2). We want to make sure that a value
/// set by command-line cannot be changed unless the update is
/// requested from another command-line.
template <typename T>
class OptionValue {
 public:
  enum class Type {
    DEFAULT,
    FROM_COMMAND_LINE,
    FROM_FILE,
  };

  /// Constructs an option value with @p value.
  explicit OptionValue(T value)
      : value_{std::move(value)}, type_{Type::DEFAULT} {}

  /// Returns the value.
  const T& get() const { return value_; }

  /// Sets the value to @p value which is given by a command-line argument.
  void set_from_command_line(const T& value) {
    value_ = value;
    type_ = Type::FROM_COMMAND_LINE;
  }

  /// Sets the value to @p value which is provided from a file.
  ///
  /// @note This operation is ignored if the current value is set by
  /// command-line.
  void set_from_file(const T& value) {
    switch (type_) {
      case Type::DEFAULT:
      case Type::FROM_FILE:
        value_ = value;
        type_ = Type::FROM_FILE;
        return;

      case Type::FROM_COMMAND_LINE:
        // No operation.
        return;
    }
  }

 private:
  T value_;
  Type type_;
};
}  // namespace dreal
