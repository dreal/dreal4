#include "dreal/smt2/driver.h"

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <utility>

#include "dreal/smt2/scanner.h"
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
using std::ostream;
using std::ostringstream;
using std::string;

Smt2Driver::Smt2Driver(Context context) : context_{move(context)} {}

bool Smt2Driver::parse_stream(istream& in, const string& sname) {
  streamname_ = sname;

  Smt2Scanner scanner(&in);
  scanner.set_debug(trace_scanning_);
  this->scanner_ = &scanner;

  Smt2Parser parser(*this);
  parser.set_debug_level(trace_parsing_);
  return (parser.parse() == 0);
}

bool Smt2Driver::parse_file(const string& filename) {
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

bool Smt2Driver::parse_string(const string& input, const string& sname) {
  istringstream iss(input);
  return parse_stream(iss, sname);
}

void Smt2Driver::error(const location& l, const string& m) {
  cerr << l << " : " << m << endl;
}

void Smt2Driver::error(const string& m) { cerr << m << endl; }

void Smt2Driver::CheckSat() {
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

namespace {
ostream& PrintModel(ostream& os, const Box& box) {
  os << "(model\n";
  for (int i = 0; i < box.size(); ++i) {
    const Variable& var{box.variable(i)};
    os << "  (define-fun " << var << " () ";
    switch (var.get_type()) {
      case Variable::Type::CONTINUOUS:
        os << Sort::Real;
        break;
      case Variable::Type::BINARY:
        os << Sort::Binary;
        break;
      case Variable::Type::INTEGER:
        os << Sort::Int;
        break;
      case Variable::Type::BOOLEAN:
        os << Sort::Bool;
        break;
    }
    os << " ";
    const Box::Interval& iv{box[i]};
    if (iv.is_degenerated()) {
      os << iv.lb();
    } else {
      os << iv;
    }
    os << ")\n";
  }
  return os << ")";
}
}  // namespace

void Smt2Driver::GetModel() {
  const Box& box{context_.get_model()};
  if (box.empty()) {
    cout << "(error \"model is not available\")" << endl;
  } else {
    PrintModel(cout, box) << endl;
  }
}

Variable Smt2Driver::RegisterVariable(const string& name, const Sort sort) {
  const Variable v{ParseVariableSort(name, sort)};
  scope_.insert(v.get_name(), v);
  return v;
}

void Smt2Driver::DeclareVariable(const string& name, const Sort sort) {
  const Variable v{RegisterVariable(name, sort)};
  context_.DeclareVariable(v);
}

void Smt2Driver::DeclareVariable(const string& name, const Sort sort,
                                 const Term& lb, const Term& ub) {
  const Variable v{RegisterVariable(name, sort)};
  context_.DeclareVariable(v, lb.expression(), ub.expression());
}

string Smt2Driver::MakeUniqueName(const string& name) {
  ostringstream oss;
  // The \ character ensures that the name cannot occur in an SMT-LIBv2 file.
  oss << "L" << nextUniqueId_++ << "\\" << name;
  return oss.str();
}

Variable Smt2Driver::DeclareLocalVariable(const string& name, const Sort sort) {
  const Variable v{ParseVariableSort(MakeUniqueName(name), sort)};
  scope_.insert(name, v);  // v is not inserted under its own name.
  context_.DeclareVariable(
      v, false /* This local variable is not a model variable. */);
  return v;
}

const Variable& Smt2Driver::lookup_variable(const string& name) {
  const auto it = scope_.find(name);
  if (it == scope_.cend()) {
    throw DREAL_RUNTIME_ERROR("{} is an undeclared variable.", name);
  }
  return it->second;
}

Variable Smt2Driver::ParseVariableSort(const string& name, const Sort s) {
  return Variable{name, SortToType(s)};
}

}  // namespace dreal
