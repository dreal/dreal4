#pragma once

#include <cassert>
#include <ostream>
#include <utility>

namespace dreal {

/// Represents an optional value in dReal. There are four ways that an
/// option can have its value -- by default, by a command-line
/// argument, by a set-info/set-option command from a .smt2 file, and
/// a manual update in a code. We define an order in these types and
/// make sure that an update is executed only if it is requested by
/// the same type or a higher type. For example, a value set by
/// command-line cannot be changed by an updated requested from a file.
template <typename T>
class OptionValue {
 public:
  enum class Type {
    DEFAULT,            ///< Default value
    FROM_FILE,          ///< Updated by a set-option/set-info in a file
    FROM_COMMAND_LINE,  ///< Updated by a command-line argument
    FROM_CODE,          ///< Explicitly updated by a code
  };

  /// Constructs an option value with @p value.
  explicit OptionValue(T value)
      : value_{std::move(value)}, type_{Type::DEFAULT} {}

  /// Default copy constructor.
  OptionValue(const OptionValue&) = default;

  /// Default move constructor.
  OptionValue(OptionValue&&) noexcept = default;

  /// Default copy assign operator.
  OptionValue& operator=(const OptionValue&) = default;

  /// Default move assign operator.
  OptionValue& operator=(OptionValue&&) noexcept = default;

  /// Default destructor.
  ~OptionValue() = default;

  /// Copy-assign operator for T.
  ///
  /// Note: It sets value with `Type::FROM_CODE` type.
  OptionValue& operator=(const T& value) {
    value_ = value;
    type_ = Type::FROM_CODE;
    return *this;
  }

  /// Move-assign operator for T.
  ///
  /// Note: It sets value with `Type::FROM_CODE` type.
  OptionValue& operator=(T&& value) {
    value_ = std::move(value);
    type_ = Type::FROM_CODE;
    return *this;
  }

  /// Returns the value.
  const T& get() const { return value_; }

  /// Sets the value to @p value which is given by a command-line argument.
  void set_from_command_line(const T& value) {
    if (type_ != Type::FROM_CODE) {
      value_ = value;
      type_ = Type::FROM_COMMAND_LINE;
    }
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
      case Type::FROM_CODE:
        // No operation.
        return;
    }
  }

  friend std::ostream& operator<<(std::ostream& os, Type type) {
    switch (type) {
      case OptionValue<T>::Type::DEFAULT:
        return os << "DEFAULT";
      case OptionValue<T>::Type::FROM_FILE:
        return os << "FROM_FILE";
      case OptionValue<T>::Type::FROM_COMMAND_LINE:
        return os << "FROM_COMMAND_LINE";
      case OptionValue<T>::Type::FROM_CODE:
        return os << "FROM_CODE";
    }
  }

 private:
  T value_;
  Type type_;
};
}  // namespace dreal
