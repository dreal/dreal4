#include <istream>
#include <string>
#include <vector>

#include "dreal/dr/location.hh"
#include "dreal/dr/scanner.h"
#include "dreal/solver/context.h"
#include "dreal/util/scoped_unordered_map.h"

namespace dreal {

/** The DrDriver class brings together all components. It creates an
 * instance of the Parser and Scanner classes and connects them. Then
 * the input stream is fed into the scanner object and the parser gets
 * it's token sequence. Furthermore the driver object is available in
 * the grammar rules as a parameter. Therefore the driver class
 * contains a reference to the structure into which the parsed data is
 * saved. */
class DrDriver {
 public:
  /// construct a new parser driver context
  DrDriver() = default;
  explicit DrDriver(Context context);

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

  /// Returns a variable associated with a name @p name.
  ///
  /// @throws if no variable is associated with @p name.
  const Variable& lookup_variable(const std::string& name);

  /// Declare a variable @p v.
  void DeclareVariable(const Variable& v);

  /// Declare a variable @p v which is bounded by an interval `[lb, ub]`.
  void DeclareVariable(const Variable& v, const Expression& lb,
                       const Expression& ub);

  /// Asserts a formula @p f.
  void Assert(const Formula& f);

  /// Asserts a formula maximizing a cost function @p f.
  void Minimize(const Expression& f);

  /// Solves the constructed problem.
  void Solve();

  /// enable debug output in the flex scanner
  bool trace_scanning_{false};

  /// enable debug output in the bison parser
  bool trace_parsing_{false};

  /// stream name (file or input stream) used for error messages.
  std::string streamname_;

  /** Pointer to the current scanenr instance, this is used to connect the
   * parser to the scanner. It is used in the yylex macro. */
  DrScanner* scanner_{nullptr};

 private:
  /** The context filled during parsing of the expressions. */
  Context context_;
  std::vector<Formula> constraints_;
  std::vector<Expression> objectives_;
  /** Scoped map from a string to a corresponding Variable. */
  ScopedUnorderedMap<std::string, Variable> scope_;
};

}  // namespace dreal
