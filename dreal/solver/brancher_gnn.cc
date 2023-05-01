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
#include <chrono>
#include <torch/torch.h>

#include <typeinfo>

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
    id2var.emplace(id, item.key());
    num_vars = std::max(num_vars, id + 1);
  }

  for (const auto& item : json["cst2ids"].items()) {
    cst2id.emplace(item.key(), item.value().get<int>());
    num_csts = std::max(num_csts, item.value().get<int>() + 1);
  }

  for (const auto& item : json["cst2edge"].items()) {
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

  auto float_opts = torch::TensorOptions().dtype(torch::kFloat32);
  auto bool_opts = torch::TensorOptions().dtype(torch::kBool);

  torch::Tensor var_mask, edge_mask, var_node_lbs, var_node_ubs, cst_node_args;
  var_mask = torch::from_blob(
    info.var_mask.data(), {1, info.graph_def.num_vars}, bool_opts);

  edge_mask = torch::from_blob(
    info.edge_mask.data(), {1, info.graph_def.num_edges}, bool_opts);

  var_node_lbs = torch::from_blob(
    info.var_node_lbs.data(), {1, info.graph_def.num_vars},
    float_opts);

  var_node_ubs = torch::from_blob(
    info.var_node_ubs.data(), {1, info.graph_def.num_vars},
    float_opts);

  cst_node_args = torch::from_blob(
    info.cst_node_args.data(),
    {1, info.graph_def.num_csts, info.graph_def.max_n_args},
    float_opts);

   std::unordered_map<std::string, torch::jit::IValue> umap = {
       {"var_mask", torch::jit::IValue(var_mask)},
       {"edge_mask", torch::jit::IValue(edge_mask)},
       {"var_node_lbs", torch::jit::IValue(var_node_lbs)},
       {"var_node_ubs", torch::jit::IValue(var_node_ubs)},
       {"cst_node_args", torch::jit::IValue(cst_node_args)}
   };

  auto start = std::chrono::steady_clock::now();
  torch::jit::IValue output = info.module->forward({}, umap);
  auto end = std::chrono::steady_clock::now();
  std::cout << "Model inference time: " <<
     std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count() << "ns\n";
  bool tuple_output = output.isTuple();
  torch::Tensor log_probs, peak;
  int branching_dim = -1;
  bool left_first = true;
  float split_value = 0.5;

  if(tuple_output){
    auto list_res = output.toTuple();
        if(list_res->elements().size() == 2){ // Gaussian distribution
            peak = list_res->elements()[0].toTensor().view(-1);
            log_probs = list_res->elements()[1].toTensor().squeeze();
        } else { // triangular distribution
            peak = list_res->elements()[1].toTensor().squeeze();
            log_probs = list_res->elements()[3].toTensor().squeeze();
        }
  } else {
    log_probs = output.toTensor();
  }

  int argmax_idx = log_probs.argmax().item<long>();
  int n_action = log_probs.sizes()[0];

  if(tuple_output){split_value = peak.index({argmax_idx}).item<float>();}

  if(n_action == static_cast<int>(info.graph_def.var2id.size())){
      branching_dim = argmax_idx;
   }
  else{
    branching_dim = argmax_idx / 2;
    left_first = static_cast<bool> (argmax_idx % 2);
  }

  // now interpret the action. The action above is indexed base on graph-def
  // but we need to return node index based on current box
  std::string node_name = info.graph_def.id2var.at(branching_dim);
  int split_dim = -1;
  for (int i = 0; i < box.size(); ++i) {
    const Variable& var_i{box.variable(i)};
    if(var_i.to_string() == node_name){split_dim=i; break;}
  }
  if (split_dim == -1){
    std::cerr << "Unable to find variable " << node_name << " in box\n";
    return -1;
  }

  // Create left and right box here:
  //  std::cout << "\nbranching dim :" << branching_dim <<
  //  "\nLeft first:" << left_first << "\n Split ratio: " << split_value << std::endl;
  pair<Box, Box> bisected_boxes{box.bisect(branching_dim, split_value)};
  if (left_first){
    *left = std::move(bisected_boxes.first);
    *right = std::move(bisected_boxes.second);
  }
  else{
    *right = std::move(bisected_boxes.first);
    *left = std::move(bisected_boxes.second);
  }
  DREAL_LOG_DEBUG(
      "Branch {}\n"
      "on {}\n"
      "Box1=\n{}\n"
      "Box2=\n{}",
      box, box.variable(branching_dim), *left, *right);
  return branching_dim;

}

}  // namespace dreal



