#include "dreal/smt2/driver.h"

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <experimental/optional>

#include "dreal/smt2/scanner.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::cout;
using std::endl;
using std::experimental::optional;
using std::ifstream;
using std::istream;
using std::istringstream;
using std::string;

Driver::Driver(const Context& context) : context_(context) {}

bool Driver::parse_stream(istream& in, const string& sname) {
  streamname_ = sname;

  Scanner scanner(&in);
  scanner.set_debug(trace_scanning_);
  this->lexer_ = &scanner;

  Parser parser(*this);
  parser.set_debug_level(trace_parsing_);
  return (parser.parse() == 0);
}

bool Driver::parse_file(const string& filename) {
  ifstream in(filename.c_str());
  if (!in.good()) return false;
  return parse_stream(in, filename);
}

bool Driver::parse_string(const string& input, const string& sname) {
  istringstream iss(input);
  return parse_stream(iss, sname);
}

void Driver::error(const class location& l, const string& m) {
  log()->error("{} : {}", l, m);
}

void Driver::error(const string& m) { log()->error("{}", m); }

void Driver::CheckSat() {
  const optional<Box> model{context_.CheckSat()};
  if (model) {
    cout << "delta-sat with delta = " << context_.config().precision() << endl;
    if (context_.config().produce_models()) {
      cout << *model << endl;
    }
  } else {
    cout << "unsat" << endl;
  }
}

}  // namespace dreal
