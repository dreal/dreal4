#include <istream>
#include <string>
#include <vector>

#include "dreal/smt2/location.hh"
#include "dreal/smt2/scanner.h"
#include "dreal/solver/context.h"
#include "dreal/util/scoped_unordered_map.h"

namespace dreal {

/** The Smt2Driver class brings together all components. It creates an
 * instance of the Parser and Scanner classes and connects them. Then
 * the input stream is fed into the scanner object and the parser gets
 * it's token sequence. Furthermore the driver object is available in
 * the grammar rules as a parameter. Therefore the driver class
 * contains a reference to the structure into which the parsed data is
 * saved. */
class Smt2Driver {
 public:
  /// construct a new parser driver context
  Smt2Driver() = default;
  explicit Smt2Driver(Context context);

  /** Invoke the scanner and parser for a stream.
   * @param in	input stream
   * @param sname	stream name for error messages
   * @return		true if successfully parsed
   */
  bool parse_stream(std::istream& in,
                    const std::string& sname = "stream input");

  /** Invoke the scanner and parser on an input string.
   * @param input	input string
   * @param sname	stream name for error messages
   * @return		true if successfully parsed
   */
  bool parse_string(const std::string& input,
                    const std::string& sname = "string stream");

  /** Invoke the scanner and parser on a file. Use parse_stream with a
   * std::ifstream if detection of file reading errors is required.
   * @param filename	input file name
   * @return		true if successfully parsed
   */
  bool parse_file(const std::string& filename);

  // To demonstrate pure handling of parse errors, instead of
  // simply dumping them on the standard error output, we will pass
  // them to the driver using the following two member functions.

  /** Error handling with associated line number. This can be modified to
   * output the error e.g. to a dialog box. */
  void error(const location& l, const std::string& m);

  /** General error handling. This can be modified to output the error
   * e.g. to a dialog box. */
  void error(const std::string& m);

  /// Calls context_.CheckSat() and print proper output messages to cout.
  void CheckSat();

  /// Declare a variable @p v.
  void DeclareVariable(const Variable& v);

  /// Declare a variable @p v which is bounded by an interval `[lb, ub]`.
  void DeclareVariable(const Variable& v, const Expression& lb,
                       const Expression& ub);

  /// Returns a variable associated with a name @p name.
  ///
  /// @throws if no variable is associated with @p name.
  const Variable& lookup_variable(const std::string& name);

  //-----------------
  // (public) Members
  //-----------------

  /// enable debug output in the flex scanner
  bool trace_scanning_{false};

  /// enable debug output in the bison parser
  bool trace_parsing_{false};

  /// stream name (file or input stream) used for error messages.
  std::string streamname_;

  /** Pointer to the current scanenr instance, this is used to connect the
   * parser to the scanner. It is used in the yylex macro. */
  Smt2Scanner* scanner_{nullptr};

  /** The context filled during parsing of the expressions. */
  Context context_;

  /** Scoped map from a string to a corresponding Variable. */
  ScopedUnorderedMap<std::string, Variable> scope_;
};

}  // namespace dreal
