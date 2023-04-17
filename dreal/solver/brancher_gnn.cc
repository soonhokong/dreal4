/*
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

#include "dreal/solver/brancher_gnn.h"

#include <algorithm>
#include <iostream>
#include <regex>
#include <stdexcept>
#include <string>
#include <vector>

#include <nlohmann/json.hpp>
#include <torch/torch.h>

#include "dreal/solver/brancher.h"
#include "dreal/util/assert.h"
#include "dreal/util/logging.h"

namespace dreal {

using std::pair;
using std::string;
using std::vector;

BranchGraphDefinition::BranchGraphDefinition(const string& filename) {
  std::ifstream ifs(filename);
  const nlohmann::json json = nlohmann::json::parse(ifs);

  for (const auto& item : json["var2id"].items()) {
    const int id{item.value().get<int>()};
    var2id.emplace(item.key(), id);
    num_vars = std::max(num_vars, id + 1);
  }

  for (const auto& item : json["cst2ids"].items()) {
    cst2id.emplace(item.key(), item.value().get<int>());
  }

  for (const auto& item : json["cst2edges"].items()) {
    vector<int> edges;
    for (const auto& element : item.value()) {
      const int id{element.get<int>()};
      edges.push_back(id);
      num_edges = std::max(num_edges, id + 1);
    }
    cst2edges.emplace(item.key(), std::move(edges));
  }
  max_n_args = json["max_n_args"].get<int>();
}

BranchTheoryLiteralPattern ExtractPattern(const Formula& f) {
  BranchTheoryLiteralPattern out;
  const std::string formula_str{f.to_string()};
  std::regex n_pattern(
      R"(([-+]?(?:(?:\d*\.\d+)|(?:\d+\.?))(?:[Ee][-+]?\d+)?))");
  std::sregex_iterator numbers(formula_str.begin(), formula_str.end(),
                               n_pattern);
  std::sregex_iterator end;

  std::vector<double> args;
  std::string abstract;
  size_t last_p = 0;

  for (; numbers != end; ++numbers) {
    std::smatch number = *numbers;
    size_t num_start = number.position();

    // Check for preceding uppercase letter
    if (num_start > 0 && isupper(formula_str[num_start - 1])) {
      continue;
    }

    args.push_back(std::stod(number.str()));
    abstract.append(formula_str.substr(last_p, num_start - last_p));
    abstract.append("{}");
    last_p = num_start + number.length();
  }

  abstract.append(formula_str.substr(last_p));
  abstract.erase(std::remove_if(abstract.begin(), abstract.end(), ::isspace),
                 abstract.end());

  out.pattern = abstract;
  out.parameters = args;

  return out;
}

int BranchGnn(const Box& box, const DynamicBitset& active_set, Box* const left,
              Box* const right, void* extra_info) {
  DREAL_ASSERT(!active_set.none());

  BranchInferenceInput& info{*(static_cast<BranchInferenceInput*>(extra_info))};

  info.var_node_lbs.resize(info.graph_def.num_vars);
  info.var_node_ubs.resize(info.graph_def.num_vars);
  for (int i = 0; i < box.size(); ++i) {
    const Variable& var_i{box.variable(i)};
    const int var_id{info.graph_def.var2id.at(var_i.to_string())};
    const Box::Interval& intv_i{box[i]};
    info.var_node_lbs[var_id] = intv_i.lb();
    info.var_node_ubs[var_id] = intv_i.ub();
  }

  // torch::jit::IValue var_mask{};
  // torch::jit::IValue edge_mask{};
  // torch::jit::IValue var_node_lbs{};
  // torch::jit::IValue var_node_ubs{};
  // torch::jit::IValue cst_node_args{};
  // std::unordered_map<std::string, torch::jit::IValue> umap = {
  //     {"var_mask", var_mask},           {"edge_mask", edge_mask},
  //     {"var_node_lbs", var_node_lbs},   {"var_node_ubs", var_node_ubs},
  //     {"cst_node_args", cst_node_args},
  // };

  // auto output = info.module.forward({}, umap);

  // interpret output...
  (void)(left);
  (void)(right);

  return -1;
}
}  // namespace dreal
