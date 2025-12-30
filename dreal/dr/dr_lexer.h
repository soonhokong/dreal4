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

#include <cstdint>
#include <istream>
#include <optional>
#include <string>
#include <variant>

namespace dreal {

// Token types for DR lexer
enum class DrTokenKind {
  Eof,
  // Literals
  Double,
  Id,
  // Keywords
  Var,
  Ctr,
  Cost,
  Prec,
  // Punctuation
  LBracket,
  RBracket,
  LParen,
  RParen,
  Colon,
  Comma,
  Semicolon,
  // Operators
  Plus,
  Minus,
  Times,
  Div,
  Caret,
  Eq,
  Lt,
  Le,
  Gt,
  Ge,
  // Boolean
  And,
  Or,
  Not,
  Implies,
  // Functions
  Exp,
  Log,
  Abs,
  Sin,
  Cos,
  Tan,
  Asin,
  Acos,
  Atan,
  Atan2,
  Sinh,
  Cosh,
  Tanh,
  Min,
  Max,
  Sqrt,
  Pow,
};

struct DrToken {
  DrTokenKind kind;
  int line{1};
  int column{1};
  std::variant<std::monostate, double, std::string> value;

  double as_double() const { return std::get<double>(value); }
  const std::string& as_string() const { return std::get<std::string>(value); }
};

class DrLexer {
 public:
  explicit DrLexer(std::istream* input);

  DrToken Next();
  const DrToken& Peek();

  void set_debug(bool v) { debug_ = v; }

  // Save/restore for backtracking
  struct State {
    size_t pos;
    int line;
    int column;
    std::optional<DrToken> peeked;
  };
  State SaveState() const { return {pos_, line_, column_, peeked_}; }
  void RestoreState(const State& s) {
    pos_ = s.pos;
    line_ = s.line;
    column_ = s.column;
    peeked_ = s.peeked;
  }

 private:
  void Advance();
  char Current() const;
  char LookAhead() const;
  bool AtEnd() const;
  void SkipWhitespaceAndComments();
  DrToken ScanToken();
  DrToken ScanNumber();
  DrToken ScanIdentifier();

  std::istream* input_;
  std::string buffer_;
  size_t pos_{0};
  int line_{1};
  int column_{1};
  std::optional<DrToken> peeked_;
  bool debug_{false};
};

}  // namespace dreal
