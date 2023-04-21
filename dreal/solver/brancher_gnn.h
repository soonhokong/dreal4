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
#pragma once

#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include <torch/script.h>

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/dynamic_bitset.h"

namespace dreal {

/// This class represents the graph definition created from Python side.
class BranchGraphDefinition {
 public:
  /// Default constructor. It sets max_n_args = -1.
  BranchGraphDefinition() {}

  /// Read the graph definition from filename (json).
  explicit BranchGraphDefinition(const std::string& filename);

  bool is_initialized() const { return max_n_args != -1; }

  std::unordered_map<std::string, int> var2id;
  std::unordered_map<int, std::string> id2var;
  std::unordered_map<std::string, int> cst2id;
  std::unordered_map<std::string, std::vector<int>> cst2edges;
  int num_vars{-1};
  int num_edges{-1};
  int max_n_args{-1};
};

/// Return type of ExtractPattern below.
struct BranchTheoryLiteralPattern {
 public:
  std::string pattern;
  std::vector<double> parameters;
};

/// Given a symbolic formula `f`, it extracts the constants in it and replace
/// each occurrence with "{}". It returns the replaced 'pattern' and the
/// extracted vector of doubles.
BranchTheoryLiteralPattern ExtractPattern(const Formula& f);

struct BranchInferenceInput {
 public:
  BranchInferenceInput(torch::jit::Module* const m,
                       const BranchGraphDefinition& g)
      : module{m}, graph_def{g} {}

  torch::jit::Module* module;

  const BranchGraphDefinition& graph_def;

  // var_mask[i] = 1 iff i-th variable is used in this theory problem.
  std::vector<int> var_mask;

  // edge_mask_[i] = 1 iff i-th edge is used in this theory problem.
  std::vector<int> edge_mask;

  // var_node_lbs_[i] is the lower bound of i-th variable in this theory
  // problem.
  std::vector<double> var_node_lbs;

  // var_node_ubs_[i] is the upper bound of i-th variable in this theory
  // problem.
  std::vector<double> var_node_ubs;

  // cst_node_args_[i] includes the parameters for i-th constraint.
  std::vector<std::vector<double>> cst_node_args;
};

/// Performs the branching operation using the trained PyTorch model.
/// It should traverse only the variables enabled by @p active_set.
///
/// @param[in] box The box to branch.
/// @param[in] active_set A subset of dimensions of the input box that is active
///                       in the given constraints.
/// @param[out] left The left sub-box.
/// @param[out] right The right sub-box.
/// @param[in]  extra_info It includes a pytorch model and tensors.
///
/// @returns the branching dimension if found, otherwise returns -1.
int BranchGnn(const Box& box, const DynamicBitset& active_set, Box* left,
              Box* right, void* extra_info);

}  // namespace dreal
