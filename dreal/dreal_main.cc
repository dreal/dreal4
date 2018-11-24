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

  auto* const positive_double_option_validator =
      new ez::ezOptionValidator("d" /* double */, "gt", "0");

  auto* const positive_int_option_validator =
      new ez::ezOptionValidator("s4" /* 4byte integer */, "gt", "0");

  opt_.add("0.001" /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Precision (default = 0.001)\n", "--precision",
           positive_double_option_validator);

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
           "Read from standard input. Uses smt2 by default.\n", "--in");

  auto* const format_option_validator =
      new ez::ezOptionValidator("t", "in", "auto,dr,smt2", false);
  opt_.add("auto" /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "File format. Any one of these (default = auto):\n"
           "smt2, dr, auto (use file extension)\n",
           "--format", format_option_validator);

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

  opt_.add("false" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Use local optimization algorithm for exist-forall problems.\n",
           "--local-optimization");

  opt_.add("1e-6" /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "[NLopt] Relative tolerance on function value (default = 1e-6)\n",
           "--nlopt-ftol-rel", positive_double_option_validator);

  opt_.add("1e-6" /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "[NLopt] Absolute tolerance on function value (default = 1e-6)\n",
           "--nlopt-ftol-abs", positive_double_option_validator);

  opt_.add("100" /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "[NLopt] Number of maximum function evaluations (default = 100)\n",
           "--nlopt-maxeval", positive_int_option_validator);

  opt_.add(
      "0.1" /* Default */, false /* Required? */,
      1 /* Number of args expected. */,
      0 /* Delimiter if expecting multiple args. */,
      "[NLopt] Maximum optimization time (in second) (default = 0.01 sec)\n",
      "--nlopt-maxtime", positive_double_option_validator);

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

  opt_.add("2" /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Set default initial phase for SAT solver.\n"
           "  0 = false\n"
           "  1 = true\n"
           "  2 = Jeroslow-Wang (default)\n"
           "  3 = random initial phase\n",
           "--sat-default-phase");

  opt_.add("0" /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Set a seed for the random number generator.", "--random-seed");
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
  if (opt_.isSet("-h") || (args_.empty() && !opt_.isSet("--in")) ||
      args_.size() > 1) {
    PrintUsage();
    return false;
  }
  return true;
}

void MainProgram::ExtractOptions() {
  // Temporary variables used to set options.
  string verbosity;
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
    double precision{0.0};
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

  // --local-optimization
  if (opt_.isSet("--local-optimization")) {
    config_.mutable_use_local_optimization().set_from_command_line(true);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --local-optimization = {}",
                    config_.use_local_optimization());
  }

  // --nlopt-ftol-rel
  double nlopt_ftol_rel{0.0};
  if (opt_.isSet("--nlopt-ftol-rel")) {
    opt_.get("--nlopt-ftol-rel")->getDouble(nlopt_ftol_rel);
    config_.mutable_nlopt_ftol_rel().set_from_command_line(nlopt_ftol_rel);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --nlopt-ftol-rel = {}",
                    config_.nlopt_ftol_rel());
  }

  // --nlopt-ftol-abs
  if (opt_.isSet("--nlopt-ftol-abs")) {
    double nlopt_ftol_abs{0.0};
    opt_.get("--nlopt-ftol-abs")->getDouble(nlopt_ftol_abs);
    config_.mutable_nlopt_ftol_abs().set_from_command_line(nlopt_ftol_abs);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --nlopt-ftol-abs = {}",
                    config_.nlopt_ftol_abs());
  }

  // --nlopt-maxeval
  if (opt_.isSet("--nlopt-maxeval")) {
    int nlopt_maxeval{0};
    opt_.get("--nlopt-maxeval")->getInt(nlopt_maxeval);
    config_.mutable_nlopt_maxeval().set_from_command_line(nlopt_maxeval);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --nlopt-maxeval = {}",
                    config_.nlopt_maxeval());
  }

  // --nlopt-maxtime
  if (opt_.isSet("--nlopt-maxtime")) {
    double nlopt_maxtime{0.0};
    opt_.get("--nlopt-maxtime")->getDouble(nlopt_maxtime);
    config_.mutable_nlopt_maxtime().set_from_command_line(nlopt_maxtime);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --nlopt-maxtime = {}",
                    config_.nlopt_maxtime());
  }

  // --sat-default-phase
  if (opt_.isSet("--sat-default-phase")) {
    int sat_default_phase{2};
    opt_.get("--sat-default-phase")->getInt(sat_default_phase);
    config_.mutable_sat_default_phase().set_from_command_line(
        static_cast<Config::SatDefaultPhase>(sat_default_phase));
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --sat-default-phase = {}",
                    config_.sat_default_phase());
  }

  // --random-seed
  if (opt_.isSet("--random-seed")) {
    // NOLINTNEXTLINE(runtime/int)
    static_assert(sizeof(unsigned long) == sizeof(std::uint64_t),
                  "sizeof(unsigned long) != sizeof(std::uint64_t).");
    // NOLINTNEXTLINE(runtime/int)
    unsigned long random_seed{0};
    opt_.get("--random-seed")->getULong(random_seed);
    config_.mutable_random_seed().set_from_command_line(random_seed);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --random-seed = {}",
                    config_.random_seed());
  }
}

int MainProgram::Run() {
  if (!is_options_all_valid_) {
    return 1;
  }
  ExtractOptions();
  string filename;
  if (!args_.empty()) {
    filename = *args_[0];
    if (filename.empty()) {
      PrintUsage();
      return 1;
    }
  }
  if (!opt_.isSet("--in") && !file_exists(filename)) {
    cerr << "File not found: " << filename << "\n" << endl;
    PrintUsage();
    return 1;
  }
  const string extension{get_extension(filename)};
  string format_opt;
  opt_.get("--format")->getString(format_opt);
  if (format_opt == "smt2" ||
      (format_opt == "auto" && (extension == "smt2" || opt_.isSet("--in")))) {
    RunSmt2(filename, config_, opt_.isSet("--debug-scanning"),
            opt_.isSet("--debug-parsing"));
  } else if (format_opt == "dr" ||
             (format_opt == "auto" && extension == "dr")) {
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
