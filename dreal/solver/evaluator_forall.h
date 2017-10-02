#pragma once

#include <memory>
#include <ostream>
#include <vector>

#include "dreal/solver/context.h"
#include "dreal/solver/evaluator.h"
#include "dreal/solver/evaluator_cell.h"
#include "dreal/solver/evaluator_quantifier_free.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

/// Evaluator for forall formulas.
///
/// In the standard first-order logic semantics, A universally
/// quantified formula is evaluated to a Boolean value. Here, however,
/// we want to have a quantitative measure when a
/// universally-quantified formula is false. We return an error
/// interval in order to utilize it as a termination criteria in ICP
/// (Interval Constraint Propagation).
///
/// Given `f = ∀y. [(e₁(x, y) ≥ 0) ∨ ... ∨ (eₙ(x, y) ≥ 0)]`, we check
/// if there is a counterexample of f. To prevent a spurious
/// counterexample, we check the satisfiability of the ε-strengthened
/// version of the negation of the nested formula, `strengthen((e₁(x,
/// y) < 0) ∧ ... ∧ (eₙ(x, y) < 0), ε)`, with delta = δ. There can be
/// two possible results for this query:
///
///  - UNSAT: Return a zero error-interval, `[0, 0]`.
///
///  - δ-SAT: Given a counter example `(a, b)`, evaluate `eᵢ(Iₓ, b)`
///           where `Iₓ` is the current interval assignment on x.
///           Returns `[0, maxᵢ{|eᵢ(Iₓ, b)|}]`.
///
class EvaluatorForall : public EvaluatorCell {
 public:
  EvaluatorForall(const Formula& f, const std::vector<Variable>& variables,
                  double epsilon, double delta);

  ~EvaluatorForall() override;

  EvaluationResult operator()(const Box& box) const override;

  std::ostream& Display(std::ostream& os) const override;

 private:
  const Formula f_;
  mutable Context context_;
  std::vector<EvaluatorQuantifierFree> evaluators_;
};
}  // namespace dreal
