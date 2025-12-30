#pragma once

#include <functional>
#include <string>
#include <unordered_map>
#include <vector>

#include "dreal/smt2/smt2_lexer.h"
#include "dreal/smt2/term.h"
#include "dreal/solver/config.h"
#include "dreal/solver/context.h"
#include "dreal/symbolic/symbolic.h"

namespace dreal {

class Smt2Parser {
 public:
  explicit Smt2Parser(std::istream* input);
  Smt2Parser(std::istream* input, const Config& config);

  void set_filename(const std::string& filename) {
    lexer_.set_filename(filename);
  }

  void set_debug_scanning(bool v) { lexer_.set_debug(v); }
  void set_debug_parsing(bool v) { debug_parsing_ = v; }

  // Parse the entire script
  void Parse();

  // Access the context
  Context& context() { return context_; }
  const Context& context() const { return context_; }

 private:
  // Parsing methods
  void ParseScript();
  void ParseCommand();
  void ParseSetLogic();
  void ParseSetInfo();
  void ParseSetOption();
  void ParseDeclareConst();
  void ParseDeclareFun();
  void ParseDefineFun();
  void ParseAssert();
  void ParseCheckSat();
  void ParseGetModel();
  void ParseGetOption();
  void ParseGetValue();
  void ParseMaximize();
  void ParseMinimize();
  void ParsePush();
  void ParsePop();
  void ParseExit();

  // Expression parsing
  Expression ParseExpr();
  Formula ParseFormula();
  Term ParseTerm();

  // Helper methods
  void Expect(TokenKind kind, const char* msg);
  void ExpectLParen();
  void ExpectRParen();
  std::string ExpectSymbol();
  double ParseNumber();
  Variable::Type ParseSort();
  Variable DeclareVariable(const std::string& name, Variable::Type type);
  Variable LookupVariable(const std::string& name);

  // Let binding support
  void PushLetScope();
  void PopLetScope();
  void AddLetBinding(const std::string& name, const Term& term);
  std::optional<Term> LookupLetBinding(const std::string& name);

  // Define-fun support
  void AddDefinedFunction(const std::string& name,
                          const std::vector<Variable>& params,
                          const Term& body);
  struct DefinedFunction {
    std::vector<Variable> params;
    Term body;
  };
  std::optional<DefinedFunction> LookupDefinedFunction(const std::string& name);

  Smt2Lexer lexer_;
  Context context_;
  std::unordered_map<std::string, Variable> variables_;
  std::vector<std::unordered_map<std::string, Term>> let_scopes_;
  std::unordered_map<std::string, DefinedFunction> defined_functions_;
  bool debug_parsing_{false};
};

}  // namespace dreal
