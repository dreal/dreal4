#include "dreal/dr/driver.h"

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <utility>

#include "dreal/dr/scanner.h"
#include "dreal/solver/expression_evaluator.h"
#include "dreal/util/optional.h"

namespace dreal {

using std::cerr;
using std::cin;
using std::cout;
using std::endl;
using std::ifstream;
using std::istream;
using std::istringstream;
using std::move;
using std::string;

DrDriver::DrDriver(Context context) : context_{move(context)} {}

bool DrDriver::parse_stream(istream& in, const string& sname) {
  streamname_ = sname;

  DrScanner scanner(&in);
  scanner.set_debug(trace_scanning_);
  this->scanner_ = &scanner;

  DrParser parser(*this);
  parser.set_debug_level(trace_parsing_);
  return (parser.parse() == 0);
}

bool DrDriver::parse_file(const string& filename) {
  if (filename.empty()) {
    // Option --in passed to dreal.
    return parse_stream(cin, "(stdin)");
  }
  ifstream in(filename.c_str());
  if (!in.good()) {
    return false;
  }
  return parse_stream(in, filename);
}

bool DrDriver::parse_string(const string& input, const string& sname) {
  istringstream iss(input);
  return parse_stream(iss, sname);
}

void DrDriver::error(const location& l, const string& m) {
  cerr << l << " : " << m << endl;
}

void DrDriver::error(const string& m) { cerr << m << endl; }

const Variable& DrDriver::lookup_variable(const std::string& name) {
  const auto it = scope_.find(name);
  if (it == scope_.cend()) {
    throw DREAL_RUNTIME_ERROR("{} is an undeclared variable.", name);
  }
  return it->second;
}

void DrDriver::DeclareVariable(const Variable& v) {
  scope_.insert(v.get_name(), v);
  context_.DeclareVariable(v);
}

void DrDriver::DeclareVariable(const Variable& v, const Expression& lb,
                               const Expression& ub) {
  scope_.insert(v.get_name(), v);
  context_.DeclareVariable(v, lb, ub);
}

void DrDriver::Assert(const Formula& f) { constraints_.push_back(f); }

void DrDriver::Minimize(const Expression& f) { objectives_.push_back(f); }

void DrDriver::Solve() {
  // Add constraints.
  for (const Formula& f : constraints_) {
    context_.Assert(f);
  }
  // Add objective functions.
  if (!objectives_.empty()) {
    context_.Minimize(objectives_);
  }
  const optional<Box> model{context_.CheckSat()};
  if (model) {
    cout << "delta-sat with delta = " << context_.config().precision() << endl;
    if (context_.config().produce_models()) {
      cout << *model << endl;
      for (const Expression& f : objectives_) {
        cout << "Found minimum for " << f << " is "
             << ExpressionEvaluator(f)(*model).mid() << endl;
      }
    }
  } else {
    cout << "unsat" << endl;
  }
  context_.Exit();
}

}  // namespace dreal
