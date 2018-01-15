#include "dreal/dreal_main.h"

#include <csignal>
#include <cstdlib>
#include <iostream>

#include "dreal/dr/run.h"
#include "dreal/smt2/run.h"
#include "dreal/solver/context.h"
#include "dreal/util/exception.h"
#include "dreal/util/filesystem.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::cerr;
using std::endl;
using std::string;
using std::vector;

MainProgram::MainProgram(int argc, const char* argv[]) {
  AddOptions();
  opt_.parse(argc, argv);  // Parse Options
  is_options_all_valid_ = ValidateOptions();
}

void MainProgram::PrintUsage() {
  string usage;
  opt_.getUsage(usage);
  cerr << usage;
}

void MainProgram::AddOptions() {
#ifndef NDEBUG
  const string build_type{"Debug"};
#else
  const string build_type{"Release"};
#endif
  opt_.overview =
      fmt::format("dReal v{} ({} Build) : delta-complete SMT solver",
                  Context::version(), build_type);
  opt_.syntax = "dreal [OPTIONS] <input file> (.smt2 or .dr)";

  // NOTE: Make sure to match the default values specified here with the ones
  // specified in dreal/solver/config.h.
  opt_.add("" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Display usage instructions.", "-h", "-help", "--help", "--usage");

  const double d[1] = {0.0};
  auto* const precision_option_validator = new ez::ezOptionValidator(
      ez::ezOptionValidator::D, ez::ezOptionValidator::GT, d, 1);

  opt_.add("0.001" /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Precision (default = 0.001)\n", "--precision",
           precision_option_validator);

  opt_.add("false" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Produce models if delta-sat\n", "--produce-models", "--model");

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

  opt_.add("false" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Use worklist fixpoint algorithm in ICP.\n", "--worklist-fixpoint");

  auto* const verbose_option_validator = new ez::ezOptionValidator(
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
  vector<string> bad_options;
  vector<string> bad_args;
  if (!opt_.gotRequired(bad_options)) {
    for (const auto& bad_option : bad_options) {
      cerr << "ERROR: Missing required option " << bad_option << ".\n\n";
    }
    PrintUsage();
    return false;
  }
  if (!opt_.gotExpected(bad_options)) {
    for (const auto& bad_option : bad_options) {
      cerr << "ERROR: Got unexpected number of arguments for option "
           << bad_option << ".\n\n";
    }
    PrintUsage();
    return false;
  }
  if (!opt_.gotValid(bad_options, bad_args)) {
    for (size_t i = 0; i < bad_options.size(); ++i) {
      cerr << "ERROR: Got invalid argument \"" << bad_args[i]
           << "\" for option " << bad_options[i] << ".\n\n";
    }
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
    log()->set_level(spdlog::level::trace);
  } else if (verbosity == "debug") {
    log()->set_level(spdlog::level::debug);
  } else if (verbosity == "info") {
    log()->set_level(spdlog::level::info);
  } else if (verbosity == "warning") {
    log()->set_level(spdlog::level::warn);
  } else if (verbosity == "error") {
    log()->set_level(spdlog::level::err);
  } else if (verbosity == "critical") {
    log()->set_level(spdlog::level::critical);
  } else {
    log()->set_level(spdlog::level::off);
  }
  // --precision
  if (opt_.isSet("--precision")) {
    opt_.get("--precision")->getDouble(precision);
    config_.mutable_precision().set_from_command_line(precision);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --precision = {}",
                    config_.precision());
  }
  // --produce-model
  if (opt_.isSet("--produce-models")) {
    config_.mutable_produce_models().set_from_command_line(true);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --produce-models = {}",
                    config_.produce_models());
  }

  // --polytope
  if (opt_.isSet("--polytope")) {
    config_.mutable_use_polytope().set_from_command_line(true);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --polytope = {}",
                    config_.use_polytope());
  }

  // --forall-polytope
  if (opt_.isSet("--forall-polytope")) {
    config_.mutable_use_polytope_in_forall().set_from_command_line(true);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --forall-polytope = {}",
                    config_.use_polytope_in_forall());
  }

  // --worklist-fixpoint
  if (opt_.isSet("--worklist-fixpoint")) {
    config_.mutable_use_worklist_fixpoint().set_from_command_line(true);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --worklist-fixpoint = {}",
                    config_.use_worklist_fixpoint());
  }
}

int MainProgram::Run() {
  if (!is_options_all_valid_) {
    return 1;
  }
  ExtractOptions();
  const string& filename{*args_[0]};
  if (!file_exists(filename)) {
    cerr << "File not found: " << filename << "\n" << endl;
    PrintUsage();
    return 1;
  }
  const string extension{get_extension(filename)};
  if (extension == "smt2") {
    RunSmt2(filename, config_, opt_.isSet("--debug-scanning"),
            opt_.isSet("--debug-parsing"));
  } else if (extension == "dr") {
    RunDr(filename, config_, opt_.isSet("--debug-scanning"),
          opt_.isSet("--debug-parsing"));
  } else {
    cerr << "Unknown extension: " << filename << "\n" << endl;
    PrintUsage();
    return 1;
  }
  return 0;
}
}  // namespace dreal

namespace {
void HandleSigInt(const int) {
  // Properly exit so that we can see stat information produced by destructors
  // even if a user press C-c.
  std::exit(1);
}
}  // namespace

int main(int argc, const char* argv[]) {
  std::signal(SIGINT, HandleSigInt);
  dreal::MainProgram main_program{argc, argv};
  return main_program.Run();
}
