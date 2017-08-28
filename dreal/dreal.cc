#include <iostream>
#include <memory>
#include <stdexcept>
#include <vector>

#include "./ezOptionParser.hpp"

#include "dreal/smt2/driver.h"
#include "dreal/util/filesystem.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::cerr;
using std::endl;
using std::make_shared;
using std::runtime_error;
using std::shared_ptr;
using std::string;
using std::vector;

/// dReal's main program. It parses options from command line and
/// process a given smt2 file.
class MainProgram {
 public:
  /// Constructs a main program using given command-line arguments.
  MainProgram(int argc, const char* argv[]);
  /// Executes a smt2 file.
  int Run();

 private:
  void PrintUsage();
  void AddOptions();
  bool ValidateOptions();
  void ExtractOptions();

  bool is_options_all_valid{true};
  ez::ezOptionParser opt_;
  vector<const string*> args_;  // List of valid option arguments.
  dreal::Driver driver_;
};

MainProgram::MainProgram(int argc, const char* argv[]) {
  AddOptions();
  opt_.parse(argc, argv);  // Parse Options
  is_options_all_valid = ValidateOptions();
  if (is_options_all_valid) {
    ExtractOptions();
  }
}

void MainProgram::PrintUsage() {
  string usage;
  opt_.getUsage(usage);
  cerr << usage;
}

void MainProgram::AddOptions() {
  opt_.overview = "dReal v4 : delta-complete SMT solver";
  opt_.syntax = "dreal [OPTIONS] <.smt2 file>";

  opt_.add("" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Display usage instructions.", "-h", "-help", "--help", "--usage");

  opt_.add("0.001" /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Set precision (default = 0.001)\n"
           "this overrides the value specified in input files",
           "--precision");

  opt_.add("false" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Produce models if delta-sat\n"
           "this overrides the value specified in input files",
           "--produce-models", "--model");

  opt_.add("false" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Debug scanning/lexing\n", "--debug-scanning");

  opt_.add("false" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */, "Debug parsing\n",
           "--debug-parsing");

  opt_.add("false" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Use polytope contractor.\n", "--polytope");

  opt_.add("false" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Use polytope contractor in forall contractor.\n",
           "--forall-polytope");

  ez::ezOptionValidator* const verbose_option_validator =
      new ez::ezOptionValidator(
          "t", "in", "trace,debug,info,warning,error,critical,off", true);
  opt_.add(
      "error",  // Default.
      0,        // Required?
      1,        // Number of args expected.
      0,        // Delimiter if expecting multiple args.
      "Verbosity level. Either one of these (default = error):\n"
      "trace, debug, info, warning, error, critical, off",  // Help description.
      "--verbose",                                          // Flag token.
      verbose_option_validator);
}

bool MainProgram::ValidateOptions() {
  // Checks bad options and bad arguments.
  vector<string> badOptions;
  vector<string> badArgs;
  if (!opt_.gotRequired(badOptions)) {
    for (size_t i = 0; i < badOptions.size(); ++i)
      cerr << "ERROR: Missing required option " << badOptions[i] << ".\n\n";
    PrintUsage();
    return false;
  }
  if (!opt_.gotExpected(badOptions)) {
    for (size_t i = 0; i < badOptions.size(); ++i)
      cerr << "ERROR: Got unexpected number of arguments for option "
           << badOptions[i] << ".\n\n";
    PrintUsage();
    return false;
  }
  if (!opt_.gotValid(badOptions, badArgs)) {
    for (size_t i = 0; i < badOptions.size(); ++i)
      cerr << "ERROR: Got invalid argument \"" << badArgs[i] << "\" for option "
           << badOptions[i] << ".\n\n";
    PrintUsage();
    return false;
  }
  // After filtering out bad options/arguments, save the valid ones in `args_`.
  args_.insert(args_.end(), opt_.firstArgs.begin() + 1, opt_.firstArgs.end());
  args_.insert(args_.end(), opt_.unknownArgs.begin(), opt_.unknownArgs.end());
  args_.insert(args_.end(), opt_.lastArgs.begin(), opt_.lastArgs.end());
  if (opt_.isSet("-h") || args_.size() != 1) {
    PrintUsage();
    return false;
  }
  return true;
}

void MainProgram::ExtractOptions() {
  // Temporary variables used to set options.
  string verbosity;
  double precision{0.0};

  opt_.get("--verbose")->getString(verbosity);
  if (verbosity == "trace") {
    dreal::log()->set_level(spdlog::level::trace);
  } else if (verbosity == "debug") {
    dreal::log()->set_level(spdlog::level::debug);
  } else if (verbosity == "info") {
    dreal::log()->set_level(spdlog::level::info);
  } else if (verbosity == "warning") {
    dreal::log()->set_level(spdlog::level::warn);
  } else if (verbosity == "error") {
    dreal::log()->set_level(spdlog::level::err);
  } else if (verbosity == "critical") {
    dreal::log()->set_level(spdlog::level::critical);
  } else {
    dreal::log()->set_level(spdlog::level::off);
  }
  // --debug-scanning
  driver_.trace_scanning_ = opt_.isSet("--debug-scanning");
  DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --debug-scanning = {}",
                  driver_.trace_scanning_);
  // --debug-parsing
  driver_.trace_parsing_ = opt_.isSet("--debug-parsing");
  DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --debug-parsing = {}",
                  driver_.trace_parsing_);
  // --precision
  opt_.get("--precision")->getDouble(precision);
  driver_.context_.get_mutable_config().set_precision(precision);
  DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --precision = {}",
                  driver_.context_.config().precision());
  // --produce-model
  driver_.context_.get_mutable_config().set_produce_models(
      opt_.isSet("--produce-models"));
  DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --produce-models = {}",
                  driver_.context_.config().produce_models());

  // --polytope
  driver_.context_.get_mutable_config().set_use_polytope(
      opt_.isSet("--polytope"));
  DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --polytope = {}",
                  driver_.context_.config().use_polytope());

  // --forall-polytope
  driver_.context_.get_mutable_config().set_use_polytope_in_forall(
      opt_.isSet("--forall-polytope"));
  DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --forall-polytope = {}",
                  driver_.context_.config().use_polytope_in_forall());
}

int MainProgram::Run() {
  if (!is_options_all_valid) {
    return 1;
  }
  // TODO(soonho): Set up version string.
  const string& filename{*args_[0]};
  if (!dreal::file_exists(filename)) {
    cerr << "File not found: " << filename << "\n" << endl;
    PrintUsage();
    return 1;
  }
  // For now, the parser calls solving process. We might need to
  // change it later.
  driver_.parse_file(filename);
  return 0;
}
}  // namespace dreal

int main(int argc, const char* argv[]) {
  dreal::MainProgram main_program{argc, argv};
  return main_program.Run();
}
