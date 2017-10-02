#pragma once

#include <memory>
#include <ostream>
#include <vector>

#include "./ibex.h"

#include "dreal/solver/evaluator.h"
#include "dreal/solver/evaluator_cell.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"
#include "dreal/util/ibex_converter.h"

namespace dreal {
/// Evaluator for quantifier-free formulas. It uses IBEX's function
/// evaluation to evaluate QF-formulas.
class EvaluatorQuantifierFree : public EvaluatorCell {
 public:
  ~EvaluatorQuantifierFree() override;

  EvaluatorQuantifierFree(const Formula& f,
                          const std::vector<Variable>& variables);

  EvaluationResult operator()(const Box& box) const override;

  std::ostream& Display(std::ostream& os) const override;

 private:
  const std::shared_ptr<IbexConverter> ibex_converter_;
  RelationalOperator op_{};
  std::shared_ptr<ibex::Function> func_;
};
}  // namespace dreal
