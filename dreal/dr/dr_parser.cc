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
#include "dreal/dr/dr_parser.h"

#include <cmath>
#include <iostream>
#include <stdexcept>

#include "dreal/solver/expression_evaluator.h"
#include "dreal/util/exception.h"

namespace dreal {

DrParser::DrParser(std::istream* input) : lexer_(input) {}

DrParser::DrParser(std::istream* input, const Config& config)
    : lexer_(input), context_(config) {}

void DrParser::set_debug_scanning(bool v) { lexer_.set_debug(v); }

void DrParser::Expect(DrTokenKind kind, const char* msg) {
  DrToken t = lexer_.Next();
  if (t.kind != kind) {
    throw DREAL_RUNTIME_ERROR("Parse error at {}:{}: {}", t.line, t.column,
                              msg);
  }
}

void DrParser::Parse() {
  ParseScript();
  Solve();
}

void DrParser::ParseScript() {
  Expect(DrTokenKind::Var, "expected 'var'");
  Expect(DrTokenKind::Colon, "expected ':'");
  ParseVarSection();

  if (lexer_.Peek().kind == DrTokenKind::Ctr) {
    lexer_.Next();
    Expect(DrTokenKind::Colon, "expected ':'");
    ParseCtrSection();
  }

  if (lexer_.Peek().kind == DrTokenKind::Cost) {
    lexer_.Next();
    Expect(DrTokenKind::Colon, "expected ':'");
    ParseCostSection();
  }
}

void DrParser::ParseVarSection() {
  while (lexer_.Peek().kind != DrTokenKind::Ctr &&
         lexer_.Peek().kind != DrTokenKind::Cost &&
         lexer_.Peek().kind != DrTokenKind::Eof) {
    ParseVarDecl();
  }
}

void DrParser::ParseVarDecl() {
  double lb, ub;

  if (lexer_.Peek().kind == DrTokenKind::LBracket) {
    lexer_.Next();
    lb = ParseExpr().Evaluate();
    Expect(DrTokenKind::Comma, "expected ','");
    ub = ParseExpr().Evaluate();
    Expect(DrTokenKind::RBracket, "expected ']'");
  } else {
    double val = ParseExpr().Evaluate();
    lb = ub = val;
  }

  DrToken name_tok = lexer_.Next();
  if (name_tok.kind != DrTokenKind::Id) {
    throw DREAL_RUNTIME_ERROR("Parse error at {}:{}: expected identifier",
                              name_tok.line, name_tok.column);
  }
  Expect(DrTokenKind::Semicolon, "expected ';'");

  Variable v{name_tok.as_string(), Variable::Type::CONTINUOUS};
  variables_[name_tok.as_string()] = v;
  context_.DeclareVariable(v, Expression{lb}, Expression{ub});
}

void DrParser::ParseCtrSection() {
  while (lexer_.Peek().kind != DrTokenKind::Cost &&
         lexer_.Peek().kind != DrTokenKind::Eof) {
    ParseCtrDecl();
  }
}

void DrParser::ParseCtrDecl() {
  Formula f = ParseFormula();
  Expect(DrTokenKind::Semicolon, "expected ';'");
  constraints_.push_back(f);
}

void DrParser::ParseCostSection() {
  while (lexer_.Peek().kind != DrTokenKind::Eof) {
    ParseCostDecl();
  }
}

void DrParser::ParseCostDecl() {
  Expression e = ParseExpr();
  Expect(DrTokenKind::Semicolon, "expected ';'");
  objectives_.push_back(e);
}

Formula DrParser::ParseFormula() {
  Formula left = ParseFormulaOr();
  while (lexer_.Peek().kind == DrTokenKind::Implies) {
    lexer_.Next();
    Formula right = ParseFormulaOr();
    left = !left || right;
  }
  return left;
}

Formula DrParser::ParseFormulaOr() {
  Formula left = ParseFormulaAnd();
  while (lexer_.Peek().kind == DrTokenKind::Or) {
    lexer_.Next();
    Formula right = ParseFormulaAnd();
    left = left || right;
  }
  return left;
}

Formula DrParser::ParseFormulaAnd() {
  Formula left = ParseFormulaNot();
  while (lexer_.Peek().kind == DrTokenKind::And) {
    lexer_.Next();
    Formula right = ParseFormulaNot();
    left = left && right;
  }
  return left;
}

Formula DrParser::ParseFormulaNot() {
  if (lexer_.Peek().kind == DrTokenKind::Not) {
    lexer_.Next();
    return !ParseFormulaNot();
  }
  return ParseFormulaAtom();
}

Formula DrParser::ParseFormulaAtom() {
  // A formula atom is either:
  // 1. (formula) - parenthesized formula
  // 2. expr op expr - comparison
  // The ambiguity is when we see ( - it could be (formula) or (expr) op expr
  // We use backtracking: try to parse as (formula), if that fails, parse as
  // expr op expr

  if (lexer_.Peek().kind == DrTokenKind::LParen) {
    // Save state for potential backtrack
    auto saved = lexer_.SaveState();
    lexer_.Next();  // consume (

    // Try to parse as formula
    try {
      Formula f = ParseFormula();
      if (lexer_.Peek().kind == DrTokenKind::RParen) {
        lexer_.Next();  // consume )
        return f;
      }
    } catch (...) {
      // Parsing as formula failed, will try as expression
    }

    // Restore and try as expression
    lexer_.RestoreState(saved);
  }

  // Parse as expr op expr
  Expression left = ParseExpr();
  DrToken op = lexer_.Next();
  Expression right = ParseExpr();

  switch (op.kind) {
    case DrTokenKind::Eq:
      return left == right;
    case DrTokenKind::Lt:
      return left < right;
    case DrTokenKind::Le:
      return left <= right;
    case DrTokenKind::Gt:
      return left > right;
    case DrTokenKind::Ge:
      return left >= right;
    default:
      throw DREAL_RUNTIME_ERROR("Parse error at {}:{}: expected comparison",
                                op.line, op.column);
  }
}

Expression DrParser::ParseExpr() { return ParseExprAddSub(); }

Expression DrParser::ParseExprAddSub() {
  Expression left = ParseExprMulDiv();
  while (lexer_.Peek().kind == DrTokenKind::Plus ||
         lexer_.Peek().kind == DrTokenKind::Minus) {
    DrToken op = lexer_.Next();
    Expression right = ParseExprMulDiv();
    if (op.kind == DrTokenKind::Plus) {
      left = left + right;
    } else {
      left = left - right;
    }
  }
  return left;
}

Expression DrParser::ParseExprMulDiv() {
  Expression left = ParseExprUnary();
  while (lexer_.Peek().kind == DrTokenKind::Times ||
         lexer_.Peek().kind == DrTokenKind::Div) {
    DrToken op = lexer_.Next();
    Expression right = ParseExprUnary();
    if (op.kind == DrTokenKind::Times) {
      left = left * right;
    } else {
      left = left / right;
    }
  }
  return left;
}

Expression DrParser::ParseExprUnary() {
  if (lexer_.Peek().kind == DrTokenKind::Minus) {
    lexer_.Next();
    return -ParseExprUnary();
  }
  return ParseExprPow();
}

Expression DrParser::ParseExprPow() {
  Expression base = ParseExprPrimary();
  if (lexer_.Peek().kind == DrTokenKind::Caret) {
    lexer_.Next();
    Expression exp = ParseExprPow();
    return pow(base, exp);
  }
  return base;
}

Expression DrParser::ParseExprPrimary() {
  DrToken t = lexer_.Peek();

  if (t.kind == DrTokenKind::Double) {
    lexer_.Next();
    return Expression{t.as_double()};
  }

  if (t.kind == DrTokenKind::Id) {
    lexer_.Next();
    auto it = variables_.find(t.as_string());
    if (it == variables_.end()) {
      throw DREAL_RUNTIME_ERROR("Undefined variable: {}", t.as_string());
    }
    return Expression{it->second};
  }

  if (t.kind == DrTokenKind::LParen) {
    lexer_.Next();
    Expression e = ParseExpr();
    Expect(DrTokenKind::RParen, "expected ')'");
    return e;
  }

  // Function calls
  DrTokenKind func = t.kind;
  switch (func) {
    case DrTokenKind::Exp:
    case DrTokenKind::Log:
    case DrTokenKind::Abs:
    case DrTokenKind::Sin:
    case DrTokenKind::Cos:
    case DrTokenKind::Tan:
    case DrTokenKind::Asin:
    case DrTokenKind::Acos:
    case DrTokenKind::Atan:
    case DrTokenKind::Sinh:
    case DrTokenKind::Cosh:
    case DrTokenKind::Tanh:
    case DrTokenKind::Sqrt: {
      lexer_.Next();
      Expect(DrTokenKind::LParen, "expected '('");
      Expression arg = ParseExpr();
      Expect(DrTokenKind::RParen, "expected ')'");
      switch (func) {
        case DrTokenKind::Exp:
          return exp(arg);
        case DrTokenKind::Log:
          return log(arg);
        case DrTokenKind::Abs:
          return abs(arg);
        case DrTokenKind::Sin:
          return sin(arg);
        case DrTokenKind::Cos:
          return cos(arg);
        case DrTokenKind::Tan:
          return tan(arg);
        case DrTokenKind::Asin:
          return asin(arg);
        case DrTokenKind::Acos:
          return acos(arg);
        case DrTokenKind::Atan:
          return atan(arg);
        case DrTokenKind::Sinh:
          return sinh(arg);
        case DrTokenKind::Cosh:
          return cosh(arg);
        case DrTokenKind::Tanh:
          return tanh(arg);
        case DrTokenKind::Sqrt:
          return sqrt(arg);
        default:
          break;
      }
      break;
    }
    case DrTokenKind::Atan2:
    case DrTokenKind::Min:
    case DrTokenKind::Max:
    case DrTokenKind::Pow: {
      lexer_.Next();
      Expect(DrTokenKind::LParen, "expected '('");
      Expression arg1 = ParseExpr();
      Expect(DrTokenKind::Comma, "expected ','");
      Expression arg2 = ParseExpr();
      Expect(DrTokenKind::RParen, "expected ')'");
      switch (func) {
        case DrTokenKind::Atan2:
          return atan2(arg1, arg2);
        case DrTokenKind::Min:
          return min(arg1, arg2);
        case DrTokenKind::Max:
          return max(arg1, arg2);
        case DrTokenKind::Pow:
          return pow(arg1, arg2);
        default:
          break;
      }
      break;
    }
    default:
      break;
  }

  throw DREAL_RUNTIME_ERROR("Parse error at {}:{}: unexpected token", t.line,
                            t.column);
}

void DrParser::Solve() {
  for (const Formula& f : constraints_) {
    context_.Assert(f);
  }
  if (!objectives_.empty()) {
    context_.Minimize(objectives_);
  }
  const auto model = context_.CheckSat();
  if (model) {
    std::cout << "delta-sat with delta = " << context_.config().precision()
              << std::endl;
    if (context_.config().produce_models()) {
      std::cout << *model << std::endl;
      for (const Expression& f : objectives_) {
        std::cout << "Found minimum for " << f << " is "
                  << ExpressionEvaluator(f)(*model).mid() << std::endl;
      }
    }
  } else {
    std::cout << "unsat" << std::endl;
  }
}

}  // namespace dreal
