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

#include <string>
#include <unordered_map>
#include <vector>

#include "dreal/dr/dr_lexer.h"
#include "dreal/solver/config.h"
#include "dreal/solver/context.h"
#include "dreal/symbolic/symbolic.h"

namespace dreal {

class DrParser {
 public:
  explicit DrParser(std::istream* input);
  DrParser(std::istream* input, const Config& config);

  void Parse();

  void set_debug_scanning(bool v);
  void set_debug_parsing(bool v) { debug_parsing_ = v; }

 private:
  void ParseScript();
  void ParseVarSection();
  void ParseVarDecl();
  void ParseCtrSection();
  void ParseCtrDecl();
  void ParseCostSection();
  void ParseCostDecl();

  Expression ParseExpr();
  Expression ParseExprAddSub();
  Expression ParseExprMulDiv();
  Expression ParseExprUnary();
  Expression ParseExprPow();
  Expression ParseExprPrimary();

  Formula ParseFormula();
  Formula ParseFormulaOr();
  Formula ParseFormulaAnd();
  Formula ParseFormulaNot();
  Formula ParseFormulaAtom();

  void Expect(DrTokenKind kind, const char* msg);
  void Solve();

  DrLexer lexer_;
  Context context_;
  std::unordered_map<std::string, Variable> variables_;
  std::vector<Formula> constraints_;
  std::vector<Expression> objectives_;
  bool debug_parsing_{false};
};

}  // namespace dreal
