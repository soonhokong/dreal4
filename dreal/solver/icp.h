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
#pragma once

#include <vector>

#include "dreal/contractor/contractor.h"
#include "dreal/contractor/contractor_status.h"
#include "dreal/solver/config.h"
#include "dreal/solver/formula_evaluator.h"
#include "dreal/util/box.h"
#include "dreal/util/dynamic_bitset.h"
#include "dreal/util/optional.h"

namespace dreal {

/// Abstract Class for ICP (Interval Constraint Propagation) algorithm.
class Icp {
 public:
  /// Constructs an Icp based on @p config.
  explicit Icp(const Config& config);
  Icp(const Icp&) = default;
  Icp(Icp&&) = default;
  Icp& operator=(const Icp&) = delete;
  Icp& operator=(Icp&&) = delete;

  virtual ~Icp() = default;

  /// Checks the delta-satisfiability of the current assertions.
  ///
  /// @param[in] contractor Contractor to use in pruning phase
  /// @param[in] formula_evaluators A vector of FormulaEvaluator which
  ///                               determines when to stop and which
  ///                               dimension to branch.
  /// @param[in] info Extra information that can be used during CheckSat.
  /// @param[in,out] cs A contractor to be updated.
  /// Returns true  if it's delta-SAT.
  /// Returns false if it's UNSAT.
  virtual bool CheckSat(const Contractor& contractor,
                        const std::vector<FormulaEvaluator>& formula_evaluators,
                        void* info, ContractorStatus* cs) = 0;

 protected:
  const Config& config() const { return config_; }

 private:
  const Config& config_;
};

/// Evaluates each formula with @p box using interval
/// arithmetic. There are three possible outcomes:
///
/// Returns None                if there is fᵢ such that fᵢ(box) is empty.
///                             (This indicates the problem is UNSAT)
///
/// Returns Some(∅)             if for all fᵢ, we have either
///                             1) fᵢ(x) is valid for all x ∈ B *or*
///                             2) |fᵢ(B)| ≤ δ.
///                             (This indicates the problem is delta-SAT)
///
/// Returns Some(Vars)          if there is fᵢ such that
///                             1) Interval arithmetic can't validate that
///                                fᵢ(x) is valid for all x ∈ B *and*
///                             2) |fᵢ(B)| > δ.
///                             Vars = {v | v ∈ fᵢ ∧ |fᵢ(B)| > δ for all
///                             fᵢs}.
///
///                             It cannot conclude if the constraint
///                             is satisfied or not completely. It
///                             checks the width/diameter of the
///                             interval evaluation and adds the free
///                             variables in the constraint into the
///                             set that it will return.
///
/// If it returns an DynamicBitset, it represents the dimensions on
/// which the ICP algorithm needs to consider branching.
///
/// It sets @p cs's box empty if it detects UNSAT. It also calls
/// cs->AddUsedConstraint to store the constraint that is responsible
/// for the UNSAT.
optional<DynamicBitset> EvaluateBox(
    const std::vector<FormulaEvaluator>& formula_evaluators, const Box& box,
    double precision, ContractorStatus* cs);

}  // namespace dreal
