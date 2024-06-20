/*
   Copyright 2017 Toyota Research Institute
   Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
#include "dreal/dreal_main.h"

#include <csignal>
#include <cstdlib>
#include <iostream>

#include <fmt/format.h>

#include "dreal/dr/run.h"
#include "dreal/smt2/run.h"
#include "dreal/solver/brancher.h"
#include "dreal/solver/brancher_gnn.h"
#include "dreal/solver/config.h"
#include "dreal/solver/context.h"
#include "dreal/util/exception.h"
#include "dreal/util/filesystem.h"
#include "dreal/util/logging.h"
#include <torch/csrc/jit/runtime/graph_executor.h>

namespace dreal {

using std::cerr;
using std::cout;
using std::endl;
using std::string;
using std::vector;

namespace {
string get_version_string() {
#ifndef NDEBUG
  const string build_type{"Debug"};
#else
  const string build_type{"Release"};
#endif
  return fmt::format("v{} ({} Build)", Context::version(), build_type);
}
}  // namespace

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
  opt_.overview =
      fmt::format("dReal {} : delta-complete SMT solver", get_version_string());
  opt_.syntax = "dreal [OPTIONS] <input file> (.smt2 or .dr)";

  opt_.add("" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Display usage instructions.", "-h", "-help", "--help", "--usage");

  opt_.add("" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Print version number of dReal.", "-v", "--version");

  auto* const positive_double_option_validator =
      new ez::ezOptionValidator("d" /* double */, "gt", "0");

  auto* const positive_int_option_validator =
      new ez::ezOptionValidator("s4" /* 4byte integer */, "gt", "0");

  const string kDefaultPrecision{fmt::format("{}", Config::kDefaultPrecision)};
  opt_.add(kDefaultPrecision.c_str() /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           fmt::format("Precision (default = {})\n", kDefaultPrecision).c_str(),
           "--precision", positive_double_option_validator);

  opt_.add("false" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Produce models if delta-sat\n", "--produce-models", "--model");

  opt_.add("false" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Strictly follow the smtlib2 standard.\n", "--smtlib2-compliant");

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

  opt_.add("false" /* Default */, false /* Required? */,
           0 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           "Dump theory literals.\n", "--dump-theory-literals");

  opt_.add("1" /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */, "Number of jobs.\n",
           "--jobs", "-j");

  const string kDefaultNloptFtolRel{
      fmt::format("{}", Config::kDefaultNloptFtolRel)};
  opt_.add(kDefaultNloptFtolRel.c_str() /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           fmt::format(
               "[NLopt] Relative tolerance on function value (default = {})\n",
               kDefaultNloptFtolRel)
               .c_str(),
           "--nlopt-ftol-rel", positive_double_option_validator);

  const string kDefaultNloptFtolAbs{
      fmt::format("{}", Config::kDefaultNloptFtolAbs)};
  opt_.add(kDefaultNloptFtolAbs.c_str() /* Default */, false /* Required? */,
           1 /* Number of args expected. */,
           0 /* Delimiter if expecting multiple args. */,
           fmt::format(
               "[NLopt] Absolute tolerance on function value (default = {})\n",
               kDefaultNloptFtolAbs)
               .c_str(),
           "--nlopt-ftol-abs", positive_double_option_validator);

  const string kDefaultNloptMaxEval{
      fmt::format("{}", Config::kDefaultNloptMaxEval)};
  opt_.add(
      kDefaultNloptMaxEval.c_str() /* Default */, false /* Required? */,
      1 /* Number of args expected. */,
      0 /* Delimiter if expecting multiple args. */,
      fmt::format(
          "[NLopt] Number of maximum function evaluations (default = {})\n",
          kDefaultNloptMaxEval)
          .c_str(),
      "--nlopt-maxeval", positive_int_option_validator);

  const string kDefaultNloptMaxTime{
      fmt::format("{}", Config::kDefaultNloptMaxTime)};
  opt_.add(
      kDefaultNloptMaxTime.c_str() /* Default */, false /* Required? */,
      1 /* Number of args expected. */,
      0 /* Delimiter if expecting multiple args. */,
      fmt::format(
          "[NLopt] Maximum optimization time (in second) (default = {} sec)\n",
          kDefaultNloptMaxTime)
          .c_str(),
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

  opt_.add("",  // Default.
           0,   // Required?
           1,   // Number of args expected.
           0,   // Delimiter if expecting multiple args.
           "PyTorch model (.pt) to use in GNN branching.",  // Help description.
           "--branching-model");

  opt_.add("",  // Default.
           0,   // Required?
           1,   // Number of args expected.
           0,   // Delimiter if expecting multiple args.
           "Graph definition to use in GNN branching.",  // Help description.
           "--branching-graph");
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
  if (opt_.isSet("--version")) {
    return true;
  }
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

  // --smt2-compliant
  if (opt_.isSet("--smtlib2-compliant")) {
    config_.mutable_smtlib2_compliant().set_from_command_line(true);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --smtlib2-compliant = {}",
                    config_.smtlib2_compliant());
  }

  // --polytope
  if (opt_.isSet("--polytope")) {
    config_.mutable_use_polytope().set_from_command_line(true);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --polytope = {}",
                    config_.use_polytope());
  }

  // --jobs
  if (opt_.isSet("--jobs")) {
    int jobs{};
    opt_.get("--jobs")->getInt(jobs);
    config_.mutable_number_of_jobs().set_from_command_line(jobs);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --jobs = {}",
                    config_.number_of_jobs());
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

  // --dump-theory-literals
  if (opt_.isSet("--dump-theory-literals")) {
    config_.mutable_dump_theory_literals().set_from_command_line(true);
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --dump-theory-literals = {}",
                    config_.dump_theory_literals());
  }

  // --nlopt-ftol-rel
  if (opt_.isSet("--nlopt-ftol-rel")) {
    double nlopt_ftol_rel{0.0};
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

  // --branching-model
  if (opt_.isSet("--branching-model")) {
    string branching_model_filename;
    opt_.get("--branching-model")->getString(branching_model_filename);
    try {
      // the next line will make the first inference call to the model faster
      // (maybe 10x), at the cost of remaining calls will be slower (1.5x).
      torch::jit::setGraphExecutorOptimize(false);
      config_.mutable_branching_model().set_from_command_line(
          std::make_shared<torch::jit::Module>(
              torch::jit::load(branching_model_filename)));

      config_.mutable_brancher().set_from_command_line(BranchGnn);
    } catch (const c10::Error& e) {
      std::cerr << "error loading the model\n";
    }
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --branching-model = {}",
                    branching_model_filename);
  }

  // --branching-graph
  if (opt_.isSet("--branching-graph")) {
    string branching_graph_filename;
    opt_.get("--branching-graph")->getString(branching_graph_filename);
    config_.mutable_branching_graph().set_from_command_line(
        BranchGraphDefinition{branching_graph_filename});
    DREAL_LOG_DEBUG("MainProgram::ExtractOptions() --branching-graph = {}",
                    branching_graph_filename);
  }
}

int MainProgram::Run() {
  if (opt_.isSet("--version")) {
    cout << "dReal " << get_version_string() << endl;
    return 0;
  }
  if (opt_.isSet("--help")) {
    return 0;
  }
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
