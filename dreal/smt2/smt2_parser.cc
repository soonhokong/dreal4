#include "dreal/smt2/smt2_parser.h"

#include <cmath>
#include <iostream>
#include <limits>
#include <sstream>
#include <stdexcept>

#ifdef __clang__
#pragma clang diagnostic push
#if __has_warning("-Wdeprecated-literal-operator")
#pragma clang diagnostic ignored "-Wdeprecated-literal-operator"
#endif
#endif
#include <gmpxx.h>
#ifdef __clang__
#pragma clang diagnostic pop
#endif

#include "dreal/smt2/logic.h"
#include "dreal/smt2/term.h"
#include "dreal/solver/expression_evaluator.h"
#include "dreal/symbolic/prefix_printer.h"
#include "dreal/util/exception.h"
#include "dreal/util/precision_guard.h"
#include "dreal/util/string_to_interval.h"

namespace dreal {

namespace {
std::string MpzToString(const mpz_class& z) {
  if (sgn(z) == -1) {
    mpz_class neg = -z;
    return "(- " + neg.get_str() + ")";
  }
  return z.get_str();
}

std::string ToRational(const double d) {
  const mpq_class r{d};
  if (r.get_den() == 1) {
    return MpzToString(r.get_num());
  } else {
    return "(/ " + MpzToString(r.get_num()) + " " +
           MpzToString(r.get_den()) + ")";
  }
}

std::string IntervalToString(const Box::Interval& iv) {
  if (iv.lb() == iv.ub()) {
    return ToRational(iv.lb());
  } else {
    return "(interval (closed " + ToRational(iv.lb()) + ") (closed " +
           ToRational(iv.ub()) + "))";
  }
}
}  // namespace

Smt2Parser::Smt2Parser(std::istream* input) : lexer_(input) {}

Smt2Parser::Smt2Parser(std::istream* input, const Config& config)
    : lexer_(input), context_(config) {}

void Smt2Parser::Parse() { ParseScript(); }

void Smt2Parser::ParseScript() {
  while (lexer_.Peek().kind != TokenKind::Eof) {
    ParseCommand();
  }
}

void Smt2Parser::Expect(TokenKind kind, const char* msg) {
  Token t = lexer_.Next();
  if (t.kind != kind) {
    throw DREAL_RUNTIME_ERROR("Parse error at {}:{}: {}", t.loc.line,
                              t.loc.column, msg);
  }
}

void Smt2Parser::ExpectLParen() { Expect(TokenKind::LParen, "expected '('"); }

void Smt2Parser::ExpectRParen() { Expect(TokenKind::RParen, "expected ')'"); }

std::string Smt2Parser::ExpectSymbol() {
  Token t = lexer_.Next();
  if (t.kind != TokenKind::Symbol) {
    throw DREAL_RUNTIME_ERROR("Parse error at {}:{}: expected symbol",
                              t.loc.line, t.loc.column);
  }
  return t.as_string();
}

double Smt2Parser::ParseNumber() {
  Token t = lexer_.Next();
  bool negative = false;
  if (t.kind == TokenKind::Minus) {
    negative = true;
    t = lexer_.Next();
  }
  double val = 0.0;
  if (t.kind == TokenKind::Int) {
    val = static_cast<double>(t.as_int());
  } else if (t.kind == TokenKind::Double) {
    val = std::stod(t.as_string());
  } else {
    throw DREAL_RUNTIME_ERROR("Parse error at {}:{}: expected number",
                              t.loc.line, t.loc.column);
  }
  return negative ? -val : val;
}

void Smt2Parser::ParseCommand() {
  ExpectLParen();
  Token cmd = lexer_.Next();

  if (debug_parsing_) {
    std::cerr << "Parsing command at " << cmd.loc.line << ":" << cmd.loc.column
              << std::endl;
  }

  switch (cmd.kind) {
    case TokenKind::SetLogic:
      ParseSetLogic();
      break;
    case TokenKind::SetInfo:
      ParseSetInfo();
      break;
    case TokenKind::SetOption:
      ParseSetOption();
      break;
    case TokenKind::DeclareConst:
      ParseDeclareConst();
      break;
    case TokenKind::DeclareFun:
      ParseDeclareFun();
      break;
    case TokenKind::DefineFun:
      ParseDefineFun();
      break;
    case TokenKind::Assert:
      ParseAssert();
      break;
    case TokenKind::CheckSat:
      ParseCheckSat();
      break;
    case TokenKind::GetModel:
      ParseGetModel();
      break;
    case TokenKind::GetOption:
      ParseGetOption();
      break;
    case TokenKind::GetValue:
      ParseGetValue();
      break;
    case TokenKind::Maximize:
      ParseMaximize();
      break;
    case TokenKind::Minimize:
      ParseMinimize();
      break;
    case TokenKind::Push:
      ParsePush();
      break;
    case TokenKind::Pop:
      ParsePop();
      break;
    case TokenKind::Exit:
      ParseExit();
      break;
    default:
      // Skip unknown commands by consuming until matching ')'
      int depth = 1;
      while (depth > 0) {
        Token t = lexer_.Next();
        if (t.kind == TokenKind::LParen)
          depth++;
        else if (t.kind == TokenKind::RParen)
          depth--;
        else if (t.kind == TokenKind::Eof)
          throw DREAL_RUNTIME_ERROR("Unexpected end of file");
      }
      return;  // Already consumed ')'
  }

  ExpectRParen();
}

void Smt2Parser::ParseSetLogic() {
  std::string logic_str = ExpectSymbol();
  Logic logic = parse_logic(logic_str);
  context_.SetLogic(logic);
}

void Smt2Parser::ParseSetInfo() {
  // Skip info: keyword and value
  lexer_.Next();  // keyword
  // Value can be symbol, string, or s-expr
  if (lexer_.Peek().kind == TokenKind::LParen) {
    int depth = 1;
    lexer_.Next();
    while (depth > 0) {
      Token t = lexer_.Next();
      if (t.kind == TokenKind::LParen)
        depth++;
      else if (t.kind == TokenKind::RParen)
        depth--;
    }
  } else {
    lexer_.Next();
  }
}

void Smt2Parser::ParseSetOption() {
  Token keyword = lexer_.Next();
  if (keyword.kind != TokenKind::Keyword) {
    return;
  }
  const std::string& key = keyword.as_string();
  if (key == ":precision") {
    Token val = lexer_.Next();
    double precision = 0.001;
    if (val.kind == TokenKind::Double) {
      precision = std::stod(val.as_string());
    } else if (val.kind == TokenKind::Int) {
      precision = static_cast<double>(val.as_int());
    }
    context_.mutable_config().mutable_precision().set_from_file(precision);
  } else if (key == ":produce-models") {
    Token val = lexer_.Next();
    if (val.kind == TokenKind::True) {
      context_.mutable_config().mutable_produce_models().set_from_file(true);
    }
  } else if (key == ":smtlib2_compliant") {
    Token val = lexer_.Next();
    if (val.kind == TokenKind::True) {
      context_.mutable_config().mutable_smtlib2_compliant().set_from_file(true);
    }
  } else if (key == ":local-optimization") {
    Token val = lexer_.Next();
    if (val.kind == TokenKind::True) {
      context_.mutable_config().mutable_use_local_optimization().set_from_file(
          true);
    }
  } else if (key == ":polytope") {
    Token val = lexer_.Next();
    if (val.kind == TokenKind::True) {
      context_.mutable_config().mutable_use_polytope().set_from_file(true);
    }
  } else if (key == ":forall-polytope") {
    Token val = lexer_.Next();
    if (val.kind == TokenKind::True) {
      context_.mutable_config().mutable_use_polytope_in_forall().set_from_file(
          true);
    }
  } else if (key == ":worklist-fixpoint") {
    Token val = lexer_.Next();
    if (val.kind == TokenKind::True) {
      context_.mutable_config().mutable_use_worklist_fixpoint().set_from_file(
          true);
    }
  } else {
    // Skip unknown option value
    if (lexer_.Peek().kind != TokenKind::RParen) {
      lexer_.Next();
    }
  }
}

Variable::Type Smt2Parser::ParseSort() {
  Token t = lexer_.Next();
  switch (t.kind) {
    case TokenKind::Bool:
      return Variable::Type::BOOLEAN;
    case TokenKind::Int_:
      return Variable::Type::INTEGER;
    case TokenKind::Real:
      return Variable::Type::CONTINUOUS;
    case TokenKind::Symbol:
      if (t.as_string() == "Bool")
        return Variable::Type::BOOLEAN;
      if (t.as_string() == "Int")
        return Variable::Type::INTEGER;
      if (t.as_string() == "Real")
        return Variable::Type::CONTINUOUS;
      throw DREAL_RUNTIME_ERROR("Unknown sort: {}", t.as_string());
    default:
      throw DREAL_RUNTIME_ERROR("Expected sort at {}:{}", t.loc.line,
                                t.loc.column);
  }
}

Variable Smt2Parser::DeclareVariable(const std::string& name,
                                     Variable::Type type) {
  Variable v{name, type};
  variables_[name] = v;
  context_.DeclareVariable(v);
  return v;
}

Variable Smt2Parser::LookupVariable(const std::string& name) {
  auto it = variables_.find(name);
  if (it == variables_.end()) {
    throw DREAL_RUNTIME_ERROR("Undefined variable: {}", name);
  }
  return it->second;
}

void Smt2Parser::ParseDeclareConst() {
  std::string name = ExpectSymbol();
  Variable::Type type = ParseSort();

  // Check for optional interval bounds [lb, ub]
  if (lexer_.Peek().kind == TokenKind::LBracket) {
    lexer_.Next();  // consume '['
    double lb = ParseNumber();
    Expect(TokenKind::Comma, "expected ','");
    double ub = ParseNumber();
    Expect(TokenKind::RBracket, "expected ']'");
    Variable v{name, type};
    variables_[name] = v;
    context_.DeclareVariable(v, Expression{lb}, Expression{ub});
  } else {
    DeclareVariable(name, type);
  }
}

void Smt2Parser::ParseDeclareFun() {
  std::string name = ExpectSymbol();
  ExpectLParen();  // argument sorts (should be empty for constants)
  ExpectRParen();
  Variable::Type type = ParseSort();

  // Check for optional interval bounds [lb, ub]
  if (lexer_.Peek().kind == TokenKind::LBracket) {
    lexer_.Next();  // consume '['
    double lb = ParseNumber();
    Expect(TokenKind::Comma, "expected ','");
    double ub = ParseNumber();
    Expect(TokenKind::RBracket, "expected ']'");
    Variable v{name, type};
    variables_[name] = v;
    context_.DeclareVariable(v, Expression{lb}, Expression{ub});
  } else {
    DeclareVariable(name, type);
  }
}

void Smt2Parser::ParseDefineFun() {
  std::string name = ExpectSymbol();

  // Parse parameters
  ExpectLParen();
  std::vector<Variable> params;
  while (lexer_.Peek().kind != TokenKind::RParen) {
    ExpectLParen();
    std::string param_name = ExpectSymbol();
    Variable::Type param_type = ParseSort();
    Variable param{param_name, param_type};
    params.push_back(param);
    ExpectRParen();
  }
  ExpectRParen();

  // Return sort
  Variable::Type return_type = ParseSort();

  // Add parameters to scope temporarily
  std::unordered_map<std::string, Variable> saved_vars;
  for (const auto& p : params) {
    auto it = variables_.find(p.get_name());
    if (it != variables_.end()) {
      saved_vars[p.get_name()] = it->second;
    }
    variables_[p.get_name()] = p;
  }

  // Parse body
  Term body = ParseTerm();

  // Restore scope
  for (const auto& p : params) {
    auto it = saved_vars.find(p.get_name());
    if (it != saved_vars.end()) {
      variables_[p.get_name()] = it->second;
    } else {
      variables_.erase(p.get_name());
    }
  }

  if (params.empty()) {
    // No parameters - treat as variable declaration + assertion
    Variable v{name, return_type};
    variables_[name] = v;
    context_.DeclareVariable(v);
    if (body.type() == Term::Type::FORMULA) {
      context_.Assert(v == body.formula());
    } else {
      context_.Assert(v == body.expression());
    }
  } else {
    AddDefinedFunction(name, params, body);
  }
}

void Smt2Parser::ParseAssert() {
  Formula f = ParseFormula();
  context_.Assert(f);
}

void Smt2Parser::ParseCheckSat() {
  auto result = context_.CheckSat();
  if (result) {
    const Config& config = context_.config();
    if (config.smtlib2_compliant()) {
      std::cout << "delta-sat\n";
    } else {
      std::cout << "delta-sat with delta = " << config.precision() << "\n";
      if (config.produce_models()) {
        std::cout << *result << "\n";
      }
    }
  } else {
    std::cout << "unsat\n";
  }
  std::cout.flush();
}

void Smt2Parser::ParseGetModel() {
  const Box& box = context_.get_model();
  if (box.empty()) {
    std::cout << "(error \"model is not available\")\n";
  } else {
    PrecisionGuard precision_guard(&std::cout);
    std::cout << "(model\n";
    for (int i = 0; i < box.size(); ++i) {
      const Variable& var = box.variable(i);
      std::cout << "  (define-fun " << var << " () ";
      switch (var.get_type()) {
        case Variable::Type::CONTINUOUS:
          std::cout << "Real";
          break;
        case Variable::Type::INTEGER:
          std::cout << "Int";
          break;
        case Variable::Type::BOOLEAN:
          std::cout << "Bool";
          break;
        default:
          std::cout << "Real";
      }
      std::cout << " ";
      const Box::Interval& iv = box[i];
      if (var.get_type() == Variable::Type::BOOLEAN) {
        std::cout << (iv == Box::Interval::ONE ? "true" : "false");
      } else if (iv.is_degenerated()) {
        std::cout << iv.lb();
      } else {
        std::cout << iv;
      }
      std::cout << ")\n";
    }
    std::cout << ")\n";
  }
  std::cout.flush();
}

void Smt2Parser::ParsePush() {
  Token t = lexer_.Peek();
  int n = 1;
  if (t.kind == TokenKind::Int) {
    n = static_cast<int>(lexer_.Next().as_int());
  }
  context_.Push(n);
}

void Smt2Parser::ParsePop() {
  Token t = lexer_.Peek();
  int n = 1;
  if (t.kind == TokenKind::Int) {
    n = static_cast<int>(lexer_.Next().as_int());
  }
  context_.Pop(n);
}

void Smt2Parser::ParseGetOption() {
  Token keyword = lexer_.Next();
  if (keyword.kind == TokenKind::Keyword) {
    const std::string& key = keyword.as_string();
    if (key == ":precision") {
      std::cout << context_.config().precision() << "\n";
    } else {
      std::cout << "unsupported\n";
    }
  }
  std::cout.flush();
}

void Smt2Parser::ParseGetValue() {
  const Box& box = context_.get_model();
  std::cout << "(\n";
  ExpectLParen();
  while (lexer_.Peek().kind != TokenKind::RParen) {
    Term t = ParseTerm();
    std::stringstream ss;
    PrefixPrinter pp{ss};

    if (t.type() == Term::Type::EXPRESSION) {
      pp.Print(t.expression());
      ExpressionEvaluator evaluator(t.expression());
      Box::Interval iv = evaluator(box);
      std::cout << "\t(" << ss.str() << " " << IntervalToString(iv) << ")\n";
    } else if (t.type() == Term::Type::FORMULA) {
      const Formula& f = t.formula();
      pp.Print(f);
      if (is_variable(f)) {
        const Variable& v = get_variable(f);
        std::string value =
            box[v] == Box::Interval::ONE ? "true" : "false";
        std::cout << "\t(" << ss.str() << " " << value << ")\n";
      }
    }
  }
  ExpectRParen();
  std::cout << ")\n";
  std::cout.flush();
}

void Smt2Parser::ParseMaximize() {
  Expression obj = ParseExpr();
  context_.Maximize(obj);
}

void Smt2Parser::ParseMinimize() {
  Expression obj = ParseExpr();
  context_.Minimize(obj);
}

void Smt2Parser::ParseExit() {
  // Exit command - nothing to do, parsing will stop
}

void Smt2Parser::PushLetScope() { let_scopes_.emplace_back(); }

void Smt2Parser::PopLetScope() { let_scopes_.pop_back(); }

void Smt2Parser::AddLetBinding(const std::string& name, const Term& term) {
  if (!let_scopes_.empty()) {
    let_scopes_.back()[name] = term;
  }
}

std::optional<Term> Smt2Parser::LookupLetBinding(const std::string& name) {
  for (auto it = let_scopes_.rbegin(); it != let_scopes_.rend(); ++it) {
    auto found = it->find(name);
    if (found != it->end()) {
      return found->second;
    }
  }
  return std::nullopt;
}

void Smt2Parser::AddDefinedFunction(const std::string& name,
                                    const std::vector<Variable>& params,
                                    const Term& body) {
  defined_functions_[name] = DefinedFunction{params, body};
}

std::optional<Smt2Parser::DefinedFunction> Smt2Parser::LookupDefinedFunction(
    const std::string& name) {
  auto it = defined_functions_.find(name);
  if (it != defined_functions_.end()) {
    return it->second;
  }
  return std::nullopt;
}

Term Smt2Parser::ParseTerm() {
  Token t = lexer_.Peek();

  // Numeric literal
  if (t.kind == TokenKind::Int) {
    lexer_.Next();
    return Term{Expression{static_cast<double>(t.as_int())}};
  }
  if (t.kind == TokenKind::Double) {
    lexer_.Next();
    const std::string& s = t.as_string();
    // Use StringToInterval for proper rounding of decimal literals
    const Box::Interval iv = StringToInterval(s);
    if (iv.diam() == 0) {
      return Term{Expression{iv.mid()}};
    } else {
      // Use real_constant for inexact decimals
      const double parsed = std::stod(s);
      return Term{real_constant(iv.lb(), iv.ub(), iv.lb() == parsed)};
    }
  }

  // Boolean literal
  if (t.kind == TokenKind::True) {
    lexer_.Next();
    return Term{Formula::True()};
  }
  if (t.kind == TokenKind::False) {
    lexer_.Next();
    return Term{Formula::False()};
  }

  // Symbol (variable or let binding)
  if (t.kind == TokenKind::Symbol) {
    lexer_.Next();
    std::string name = t.as_string();

    // Check let bindings first
    if (auto binding = LookupLetBinding(name)) {
      return *binding;
    }

    // Check defined functions (nullary)
    if (auto func = LookupDefinedFunction(name)) {
      if (func->params.empty()) {
        return func->body;
      }
    }

    // Variable
    Variable v = LookupVariable(name);
    if (v.get_type() == Variable::Type::BOOLEAN) {
      return Term{Formula{v}};
    }
    return Term{Expression{v}};
  }

  // S-expression
  if (t.kind == TokenKind::LParen) {
    ExpectLParen();
    Token op = lexer_.Next();

    // Let expression
    if (op.kind == TokenKind::Let) {
      // Parse all bindings first (they all see the outer scope)
      std::vector<std::pair<std::string, Term>> bindings;
      ExpectLParen();
      while (lexer_.Peek().kind != TokenKind::RParen) {
        ExpectLParen();
        std::string var_name = ExpectSymbol();
        Term val = ParseTerm();
        bindings.emplace_back(var_name, val);
        ExpectRParen();
      }
      ExpectRParen();

      // Now add all bindings to a new scope
      PushLetScope();
      for (const auto& [name, val] : bindings) {
        AddLetBinding(name, val);
      }

      Term body = ParseTerm();
      PopLetScope();
      ExpectRParen();
      return body;
    }

    // Forall quantifier
    if (op.kind == TokenKind::Forall) {
      Variables vars;
      Formula domain = Formula::True();
      ExpectLParen();
      while (lexer_.Peek().kind != TokenKind::RParen) {
        ExpectLParen();
        std::string var_name = ExpectSymbol();
        Variable::Type var_type = ParseSort();
        Variable v{var_name, var_type};
        // Check for optional bounds - create domain formula
        if (lexer_.Peek().kind == TokenKind::LBracket) {
          lexer_.Next();  // consume '['
          double lb = ParseNumber();
          Expect(TokenKind::Comma, "expected ','");
          double ub = ParseNumber();
          Expect(TokenKind::RBracket, "expected ']'");
          if (std::isfinite(lb)) {
            domain = domain && (lb <= v);
          }
          if (std::isfinite(ub)) {
            domain = domain && (v <= ub);
          }
        }
        vars.insert(v);
        variables_[var_name] = v;
        ExpectRParen();
      }
      ExpectRParen();
      Formula body = ParseFormula();
      ExpectRParen();
      // Eliminate Boolean variables by substitution
      Formula eliminated_body = body;
      for (const auto& v : vars) {
        if (v.get_type() == Variable::Type::BOOLEAN) {
          eliminated_body = eliminated_body.Substitute(v, Formula::True()) &&
                            eliminated_body.Substitute(v, Formula::False());
        }
      }
      // Use imply(domain, body) to incorporate bounds
      const Variables quantified_vars =
          intersect(vars, eliminated_body.GetFreeVariables());
      if (quantified_vars.empty()) {
        return Term{eliminated_body};
      }
      return Term{forall(quantified_vars, imply(domain, eliminated_body))};
    }

    // Exists quantifier
    if (op.kind == TokenKind::Exists) {
      Variables vars;
      Formula domain = Formula::True();
      ExpectLParen();
      while (lexer_.Peek().kind != TokenKind::RParen) {
        ExpectLParen();
        std::string var_name = ExpectSymbol();
        Variable::Type var_type = ParseSort();
        Variable v{var_name, var_type};
        // Check for optional bounds - create domain formula
        if (lexer_.Peek().kind == TokenKind::LBracket) {
          lexer_.Next();  // consume '['
          double lb = ParseNumber();
          Expect(TokenKind::Comma, "expected ','");
          double ub = ParseNumber();
          Expect(TokenKind::RBracket, "expected ']'");
          if (std::isfinite(lb)) {
            domain = domain && (lb <= v);
          }
          if (std::isfinite(ub)) {
            domain = domain && (v <= ub);
          }
        }
        vars.insert(v);
        variables_[var_name] = v;
        ExpectRParen();
      }
      ExpectRParen();
      Formula body = ParseFormula();
      ExpectRParen();
      // exists(vars, body) = !forall(vars, !body)
      // With domain: exists(vars, domain && body) =
      //   !forall(vars, !(domain && body)) = !forall(vars, !domain || !body)
      const Variables quantified_vars =
          intersect(vars, body.GetFreeVariables());
      if (quantified_vars.empty()) {
        return Term{body};
      }
      return Term{!forall(quantified_vars, imply(domain, !body))};
    }

    // Function application
    if (op.kind == TokenKind::Symbol) {
      std::string func_name = op.as_string();
      if (auto func = LookupDefinedFunction(func_name)) {
        // Parse arguments
        std::vector<Term> args;
        while (lexer_.Peek().kind != TokenKind::RParen) {
          args.push_back(ParseTerm());
        }
        ExpectRParen();

        // Substitute parameters with arguments
        if (args.size() != func->params.size()) {
          throw DREAL_RUNTIME_ERROR(
              "Wrong number of arguments for function {}", func_name);
        }

        ExpressionSubstitution expr_subst;
        FormulaSubstitution formula_subst;
        for (size_t i = 0; i < args.size(); i++) {
          const Variable& param = func->params[i];
          const Term& arg = args[i];
          if (param.get_type() == Variable::Type::BOOLEAN) {
            formula_subst.emplace(
                param, arg.type() == Term::Type::FORMULA ? arg.formula()
                                                         : Formula::True());
          } else {
            expr_subst.emplace(param, arg.type() == Term::Type::EXPRESSION
                                          ? arg.expression()
                                          : Expression{0.0});
          }
        }

        if (func->body.type() == Term::Type::EXPRESSION) {
          return Term{func->body.expression().Substitute(expr_subst)};
        } else {
          return Term{
              func->body.formula().Substitute(expr_subst, formula_subst)};
        }
      }
    }

    // Parse arguments for built-in operators
    std::vector<Term> args;
    while (lexer_.Peek().kind != TokenKind::RParen) {
      args.push_back(ParseTerm());
    }
    ExpectRParen();

    // Build expression/formula based on operator
    switch (op.kind) {
      // Arithmetic
      case TokenKind::Plus: {
        Expression result{0.0};
        for (const auto& arg : args) {
          result += arg.expression();
        }
        return Term{result};
      }
      case TokenKind::Minus: {
        if (args.size() == 1) {
          return Term{-args[0].expression()};
        }
        Expression result = args[0].expression();
        for (size_t i = 1; i < args.size(); i++) {
          result -= args[i].expression();
        }
        return Term{result};
      }
      case TokenKind::Times: {
        Expression result{1.0};
        for (const auto& arg : args) {
          result *= arg.expression();
        }
        return Term{result};
      }
      case TokenKind::Div:
        return Term{args[0].expression() / args[1].expression()};
      case TokenKind::Pow:
        return Term{pow(args[0].expression(), args[1].expression())};
      case TokenKind::Sqrt:
        return Term{sqrt(args[0].expression())};
      case TokenKind::Exp:
        return Term{exp(args[0].expression())};
      case TokenKind::Log:
        return Term{log(args[0].expression())};
      case TokenKind::Abs:
        return Term{abs(args[0].expression())};
      case TokenKind::Sin:
        return Term{sin(args[0].expression())};
      case TokenKind::Cos:
        return Term{cos(args[0].expression())};
      case TokenKind::Tan:
        return Term{tan(args[0].expression())};
      case TokenKind::Asin:
        return Term{asin(args[0].expression())};
      case TokenKind::Acos:
        return Term{acos(args[0].expression())};
      case TokenKind::Atan:
        return Term{atan(args[0].expression())};
      case TokenKind::Atan2:
        return Term{atan2(args[0].expression(), args[1].expression())};
      case TokenKind::Sinh:
        return Term{sinh(args[0].expression())};
      case TokenKind::Cosh:
        return Term{cosh(args[0].expression())};
      case TokenKind::Tanh:
        return Term{tanh(args[0].expression())};
      case TokenKind::Min:
        return Term{min(args[0].expression(), args[1].expression())};
      case TokenKind::Max:
        return Term{max(args[0].expression(), args[1].expression())};

      // Comparison
      case TokenKind::Eq:
        if (args[0].type() == Term::Type::FORMULA ||
            args[1].type() == Term::Type::FORMULA) {
          return Term{args[0].formula() == args[1].formula()};
        }
        return Term{args[0].expression() == args[1].expression()};
      case TokenKind::Lt:
        return Term{args[0].expression() < args[1].expression()};
      case TokenKind::Le:
        return Term{args[0].expression() <= args[1].expression()};
      case TokenKind::Gt:
        return Term{args[0].expression() > args[1].expression()};
      case TokenKind::Ge:
        return Term{args[0].expression() >= args[1].expression()};

      // Boolean
      case TokenKind::And: {
        Formula result = Formula::True();
        for (const auto& arg : args) {
          result = result && arg.formula();
        }
        return Term{result};
      }
      case TokenKind::Or: {
        Formula result = Formula::False();
        for (const auto& arg : args) {
          result = result || arg.formula();
        }
        return Term{result};
      }
      case TokenKind::Not:
        return Term{!args[0].formula()};
      case TokenKind::Implies:
        return Term{imply(args[0].formula(), args[1].formula())};
      case TokenKind::Xor:
        return Term{(args[0].formula() && !args[1].formula()) ||
                    (!args[0].formula() && args[1].formula())};
      case TokenKind::Ite:
        if (args[1].type() == Term::Type::FORMULA ||
            args[2].type() == Term::Type::FORMULA) {
          // (ite cond then_f else_f) = (cond => then_f) && (!cond => else_f)
          const Formula& cond = args[0].formula();
          const Formula& then_f = args[1].formula();
          const Formula& else_f = args[2].formula();
          return Term{(imply(cond, then_f) && imply(!cond, else_f))};
        }
        return Term{if_then_else(args[0].formula(), args[1].expression(),
                                 args[2].expression())};

      default:
        throw DREAL_RUNTIME_ERROR("Unknown operator at {}:{}", op.loc.line,
                                  op.loc.column);
    }
  }

  throw DREAL_RUNTIME_ERROR("Unexpected token at {}:{}", t.loc.line,
                            t.loc.column);
}

Formula Smt2Parser::ParseFormula() {
  Term t = ParseTerm();
  return t.formula();
}

Expression Smt2Parser::ParseExpr() {
  Term t = ParseTerm();
  return t.expression();
}

}  // namespace dreal
