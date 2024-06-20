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
#include "dreal/solver/config.h"

#include <fmt/format.h>
#include <fmt/ostream.h>

#include "dreal/solver/brancher_gnn.h"
#include "dreal/util/exception.h"

namespace dreal {

using std::ostream;

#if __cplusplus < 201703L
constexpr double Config::kDefaultPrecision;
constexpr double Config::kDefaultNloptFtolRel;
constexpr double Config::kDefaultNloptFtolAbs;
constexpr int Config::kDefaultNloptMaxEval;
constexpr double Config::kDefaultNloptMaxTime;
#endif

double Config::precision() const { return precision_.get(); }
OptionValue<double>& Config::mutable_precision() { return precision_; }

bool Config::produce_models() const { return produce_models_.get(); }
OptionValue<bool>& Config::mutable_produce_models() { return produce_models_; }

bool Config::use_polytope() const { return use_polytope_.get(); }
OptionValue<bool>& Config::mutable_use_polytope() { return use_polytope_; }

bool Config::use_polytope_in_forall() const {
  return use_polytope_in_forall_.get();
}
OptionValue<bool>& Config::mutable_use_polytope_in_forall() {
  return use_polytope_in_forall_;
}

bool Config::use_worklist_fixpoint() const {
  return use_worklist_fixpoint_.get();
}
OptionValue<bool>& Config::mutable_use_worklist_fixpoint() {
  return use_worklist_fixpoint_;
}

bool Config::use_local_optimization() const {
  return use_local_optimization_.get();
}
OptionValue<bool>& Config::mutable_use_local_optimization() {
  return use_local_optimization_;
}

bool Config::dump_theory_literals() const {
  return dump_theory_literals_.get();
}
OptionValue<bool>& Config::mutable_dump_theory_literals() {
  return dump_theory_literals_;
}

int Config::number_of_jobs() const { return number_of_jobs_.get(); }
OptionValue<int>& Config::mutable_number_of_jobs() { return number_of_jobs_; }

bool Config::stack_left_box_first() const {
  return stack_left_box_first_.get();
}
OptionValue<bool>& Config::mutable_stack_left_box_first() {
  return stack_left_box_first_;
}

bool Config::smtlib2_compliant() const { return smtlib2_compliant_.get(); }

OptionValue<bool>& Config::mutable_smtlib2_compliant() {
  return smtlib2_compliant_;
}

const Config::Brancher& Config::brancher() const { return brancher_.get(); }

OptionValue<Config::Brancher>& Config::mutable_brancher() { return brancher_; }

double Config::nlopt_ftol_rel() const { return nlopt_ftol_rel_.get(); }

OptionValue<double>& Config::mutable_nlopt_ftol_rel() {
  return nlopt_ftol_rel_;
}

double Config::nlopt_ftol_abs() const { return nlopt_ftol_abs_.get(); }

OptionValue<double>& Config::mutable_nlopt_ftol_abs() {
  return nlopt_ftol_abs_;
}

int Config::nlopt_maxeval() const { return nlopt_maxeval_.get(); }

OptionValue<int>& Config::mutable_nlopt_maxeval() { return nlopt_maxeval_; }

double Config::nlopt_maxtime() const { return nlopt_maxtime_.get(); }

OptionValue<double>& Config::mutable_nlopt_maxtime() { return nlopt_maxtime_; }

Config::SatDefaultPhase Config::sat_default_phase() const {
  return sat_default_phase_.get();
}

OptionValue<Config::SatDefaultPhase>& Config::mutable_sat_default_phase() {
  return sat_default_phase_;
}

uint32_t Config::random_seed() const { return random_seed_.get(); }

OptionValue<uint32_t>& Config::mutable_random_seed() { return random_seed_; }

torch::jit::Module* Config::branching_model() const {
  return branching_model_.get().get();
}

OptionValue<std::shared_ptr<torch::jit::Module>>&
Config::mutable_branching_model() {
  return branching_model_;
}

const BranchGraphDefinition& Config::branching_graph() const {
  return branching_graph_.get();
}

OptionValue<BranchGraphDefinition>& Config::mutable_branching_graph() {
  return branching_graph_;
}

std::ostream& operator<<(std::ostream& os,
                         const Config::SatDefaultPhase& sat_default_phase) {
  switch (sat_default_phase) {
    case Config::SatDefaultPhase::False:
      return os << "False";
    case Config::SatDefaultPhase::True:
      return os << "True";
    case Config::SatDefaultPhase::JeroslowWang:
      return os << "Jeroslow-Wang";
    case Config::SatDefaultPhase::RandomInitialPhase:
      return os << "Random Initial Phase";
  }
  DREAL_UNREACHABLE();
}

ostream& operator<<(ostream& os, const Config& config) {
  return os << fmt::format(
             "Config("
             "precision = {}, "
             "produce_model = {}, "
             "use_polytope = {}, "
             "use_polytope_in_forall = {}, "
             "use_worklist_fixpoint = {}, "
             "use_local_optimization = {}, "
             "dump_theory_literals = {}, "
             "number_of_jobs = {}, "
             "nlopt_ftol_rel = {}, "
             "nlopt_ftol_abs = {}, "
             "nlopt_maxeval = {}, "
             "nlopt_maxtime = {}, "
             "sat_default_phase = {}, "
             "random_seed = {}"
             ")",
             config.precision(), config.produce_models(), config.use_polytope(),
             config.use_polytope_in_forall(), config.use_worklist_fixpoint(),
             config.use_local_optimization(), config.dump_theory_literals(),
             config.number_of_jobs(), config.nlopt_ftol_rel(),
             config.nlopt_ftol_abs(), config.nlopt_maxeval(),
             config.nlopt_maxtime(), config.sat_default_phase(),
             config.random_seed());
}

}  // namespace dreal
