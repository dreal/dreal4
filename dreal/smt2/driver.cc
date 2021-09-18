/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
#include "dreal/smt2/driver.h"

#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>

#include <fmt/format.h>
#include <fmt/ostream.h>
#include <gmpxx.h>

#include "dreal/smt2/scanner.h"
#include "dreal/solver/expression_evaluator.h"
#include "dreal/symbolic/prefix_printer.h"
#include "dreal/util/optional.h"
#include "dreal/util/precision_guard.h"

namespace dreal {

using std::cerr;
using std::cin;
using std::cout;
using std::ifstream;
using std::istream;
using std::istringstream;
using std::ostream;
using std::ostringstream;
using std::runtime_error;
using std::string;
using std::stringstream;
using std::vector;

FunctionDefinition::FunctionDefinition(vector<Variable> parameters,
                                       Sort return_type, Term body)
    : parameters_{std::move(parameters)},
      return_type_{return_type},
      body_{std::move(body)} {}

Term FunctionDefinition::operator()(const vector<Term>& arguments) const {
  if (parameters_.size() != arguments.size()) {
    throw runtime_error{
        fmt::format("This function definition expects {} arguments whereas the "
                    "provided arguments are of length {}.",
                    parameters_.size(), arguments.size())};
  }

  body_.Check(return_type_);
  Term t = body_;
  for (size_t i = 0; i < parameters_.size(); ++i) {
    const Variable& param_i{parameters_[i]};
    const Term& arg_i{arguments[i]};
    arg_i.Check(param_i.get_type());
    t = t.Substitute(param_i, arg_i);
  }

  return t;
}

Smt2Driver::Smt2Driver(Context context) : context_{std::move(context)} {}

bool Smt2Driver::parse_stream(istream& in, const string& sname) {
  streamname_ = sname;

  Smt2Scanner new_scanner(&in);
  new_scanner.set_debug(trace_scanning_);
  this->scanner = &new_scanner;

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
  cerr << l << " : " << m << "\n";
}

void Smt2Driver::error(const string& m) { cerr << m << "\n"; }

void Smt2Driver::CheckSat() {
  const optional<Box> model{context_.CheckSat()};
  if (model) {
    if (context_.config().smtlib2_compliant()) {
      cout << "delta-sat\n";
    } else {
      cout << "delta-sat with delta = " << context_.config().precision()
           << "\n";
      if (context_.config().produce_models()) {
        PrecisionGuard precision_guard(&cout);
        cout << *model << "\n";
      }
    }
  } else {
    cout << "unsat\n";
  }
  cout.flush();
}

namespace {
ostream& PrintModel(ostream& os, const Box& box) {
  PrecisionGuard precision_guard(&os);
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
    if (var.get_type() == Variable::Type::BOOLEAN) {
      if (iv == Box::Interval::ONE) {
        os << "true";
      } else if (iv == Box::Interval::ZERO) {
        os << "false";
      }
    } else {
      if (iv.is_degenerated()) {
        os << iv.lb();
      } else {
        os << iv;
      }
    }
    os << ")\n";
  }
  return os << ")";
}

string ToString(const mpz_class& z) {
  if (sgn(z) == -1) {
    return fmt::format("(- {})", -z);
  }
  return fmt::format("{}", z);
}

string ToRational(const double d) {
  const mpq_class r{d};
  if (r.get_den() == 1) {
    return fmt::format("{}", ToString(r.get_num()));
  } else {
    return fmt::format("(/ {} {})", ToString(r.get_num()),
                       ToString(r.get_den()));
  }
}

// Returns the string representation of @p interval.
// It returns `(exact c)` or `(interval lb ub)`.
string ToString(const Box::Interval& interval) {
  if (interval.lb() == interval.ub()) {
    return ToRational(interval.lb());
  } else {
    return fmt::format("(interval (closed {}) (closed {}))",
                       ToRational(interval.lb()), ToRational(interval.ub()));
  }
}
}  // namespace

void Smt2Driver::GetModel() const {
  const Box& box{context_.get_model()};
  if (box.empty()) {
    cout << "(error \"model is not available\")\n";
  } else {
    PrintModel(cout, box) << "\n";
  }
  cout.flush();
}

void Smt2Driver::GetValue(const vector<Term>& term_list) const {
  const Box& box{context_.get_model()};
  fmt::print("(\n");
  for (const auto& term : term_list) {
    string term_str;
    string value_str;
    stringstream ss;
    PrefixPrinter pp{ss};

    switch (term.type()) {
      case Term::Type::EXPRESSION: {
        const Expression& e{term.expression()};
        const ExpressionEvaluator evaluator{e};
        pp.Print(e);
        term_str = ss.str();
        const Box::Interval iv{ExpressionEvaluator(term.expression())(box)};
        value_str = ToString(iv);
        break;
      }
      case Term::Type::FORMULA: {
        const Formula& f{term.formula()};
        pp.Print(f);
        term_str = ss.str();
        if (is_variable(f)) {
          value_str =
              box[get_variable(f)] == Box::Interval::ONE ? "true" : "false";
        } else {
          throw std::runtime_error(fmt::format(
              "get-value does not handle a compound formula {}.", term_str));
        }
        break;
      }
    }
    fmt::print("\t({} {})\n", term_str, value_str);
  }
  fmt::print(")\n");
  cout.flush();
}

void Smt2Driver::GetOption(const string& key) const {
  const optional<string> value{context_.GetOption(key)};
  if (value) {
    fmt::print("{}\n", *value);
  } else {
    fmt::print("unsupported\n");
  }
  cout.flush();
}

Variable Smt2Driver::RegisterVariable(const string& name, const Sort sort) {
  Variable v{ParseVariableSort(name, sort)};
  scope_.insert(v.get_name(), v);
  return v;
}

Variable Smt2Driver::DeclareVariable(const string& name, const Sort sort) {
  Variable v{RegisterVariable(name, sort)};
  context_.DeclareVariable(v);
  return v;
}

void Smt2Driver::DeclareVariable(const string& name, const Sort sort,
                                 const Term& lb, const Term& ub) {
  const Variable v{RegisterVariable(name, sort)};
  context_.DeclareVariable(v, lb.expression(), ub.expression());
}

void Smt2Driver::DefineFun(const string& name,
                           const vector<Variable>& parameters, Sort return_type,
                           const Term& body) {
  FunctionDefinition func{parameters, return_type, body};
  function_definition_map_.insert(name, func);
}

string Smt2Driver::MakeUniqueName(const string& name) {
  ostringstream oss;
  // The \ character ensures that the name cannot occur in an SMT-LIBv2 file.
  oss << "L" << nextUniqueId_++ << "\\" << name;
  return oss.str();
}

Term Smt2Driver::LookupFunction(const string& name,
                                const vector<Term>& arguments) {
  const auto it = function_definition_map_.find(name);
  if (it != function_definition_map_.end()) {
    return it->second(arguments);
  } else {
    throw runtime_error{fmt::format("No function definition for {}.", name)};
  }
}

Variable Smt2Driver::DeclareLocalVariable(const string& name, const Sort sort) {
  Variable v{ParseVariableSort(MakeUniqueName(name), sort)};
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

Formula Smt2Driver::EliminateBooleanVariables(const Variables& vars,
                                              const Formula& f) {
  Formula ret{f};
  for (const auto& b : vars) {
    if (b.get_type() == Variable::Type::BOOLEAN) {
      ret = ret.Substitute(b, Formula::True()) &&
            ret.Substitute(b, Formula::False());
    }
  }
  return ret;
}

}  // namespace dreal
