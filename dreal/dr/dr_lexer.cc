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
#include "dreal/dr/dr_lexer.h"

#include <cctype>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <unordered_map>

namespace dreal {

namespace {
const std::unordered_map<std::string, DrTokenKind> kKeywords = {
    {"var", DrTokenKind::Var},
    {"ctr", DrTokenKind::Ctr},
    {"cost", DrTokenKind::Cost},
    {"prec", DrTokenKind::Prec},
    {"and", DrTokenKind::And},
    {"or", DrTokenKind::Or},
    {"not", DrTokenKind::Not},
    {"implies", DrTokenKind::Implies},
    {"exp", DrTokenKind::Exp},
    {"log", DrTokenKind::Log},
    {"abs", DrTokenKind::Abs},
    {"sin", DrTokenKind::Sin},
    {"cos", DrTokenKind::Cos},
    {"tan", DrTokenKind::Tan},
    {"asin", DrTokenKind::Asin},
    {"arcsin", DrTokenKind::Asin},
    {"acos", DrTokenKind::Acos},
    {"arccos", DrTokenKind::Acos},
    {"atan", DrTokenKind::Atan},
    {"arctan", DrTokenKind::Atan},
    {"atan2", DrTokenKind::Atan2},
    {"arctan2", DrTokenKind::Atan2},
    {"sinh", DrTokenKind::Sinh},
    {"cosh", DrTokenKind::Cosh},
    {"tanh", DrTokenKind::Tanh},
    {"min", DrTokenKind::Min},
    {"max", DrTokenKind::Max},
    {"sqrt", DrTokenKind::Sqrt},
    {"pow", DrTokenKind::Pow},
};
}  // namespace

DrLexer::DrLexer(std::istream* input) : input_(input) {
  std::ostringstream ss;
  ss << input_->rdbuf();
  buffer_ = ss.str();
}

void DrLexer::Advance() {
  if (pos_ < buffer_.size()) {
    if (buffer_[pos_] == '\n') {
      line_++;
      column_ = 1;
    } else {
      column_++;
    }
    pos_++;
  }
}

char DrLexer::Current() const {
  return pos_ < buffer_.size() ? buffer_[pos_] : '\0';
}

char DrLexer::LookAhead() const {
  return pos_ + 1 < buffer_.size() ? buffer_[pos_ + 1] : '\0';
}

bool DrLexer::AtEnd() const { return pos_ >= buffer_.size(); }

void DrLexer::SkipWhitespaceAndComments() {
  while (!AtEnd()) {
    char c = Current();
    if (std::isspace(c)) {
      Advance();
    } else if (c == '#') {
      // Skip comment until end of line
      while (!AtEnd() && Current() != '\n') {
        Advance();
      }
    } else {
      break;
    }
  }
}

DrToken DrLexer::ScanNumber() {
  int start_line = line_;
  int start_col = column_;
  size_t start = pos_;

  // Optional sign
  if (Current() == '+' || Current() == '-') {
    Advance();
  }

  // Integer part
  while (!AtEnd() && std::isdigit(Current())) {
    Advance();
  }

  // Decimal part
  if (Current() == '.' && std::isdigit(LookAhead())) {
    Advance();
    while (!AtEnd() && std::isdigit(Current())) {
      Advance();
    }
  } else if (Current() == '.') {
    Advance();  // trailing dot like "5."
  }

  // Exponent
  if (Current() == 'e' || Current() == 'E') {
    Advance();
    if (Current() == '+' || Current() == '-') {
      Advance();
    }
    while (!AtEnd() && std::isdigit(Current())) {
      Advance();
    }
  }

  std::string num_str = buffer_.substr(start, pos_ - start);
  return DrToken{DrTokenKind::Double, start_line, start_col,
                 std::stod(num_str)};
}

DrToken DrLexer::ScanIdentifier() {
  int start_line = line_;
  int start_col = column_;
  size_t start = pos_;

  while (!AtEnd() &&
         (std::isalnum(Current()) || Current() == '_' || Current() == '.')) {
    Advance();
  }

  std::string text = buffer_.substr(start, pos_ - start);

  auto it = kKeywords.find(text);
  if (it != kKeywords.end()) {
    return DrToken{it->second, start_line, start_col, std::monostate{}};
  }

  return DrToken{DrTokenKind::Id, start_line, start_col, text};
}

DrToken DrLexer::ScanToken() {
  SkipWhitespaceAndComments();

  if (AtEnd()) {
    return DrToken{DrTokenKind::Eof, line_, column_, std::monostate{}};
  }

  int start_line = line_;
  int start_col = column_;
  char c = Current();

  // Single character tokens
  if (c == '[') {
    Advance();
    return DrToken{DrTokenKind::LBracket, start_line, start_col,
                   std::monostate{}};
  }
  if (c == ']') {
    Advance();
    return DrToken{DrTokenKind::RBracket, start_line, start_col,
                   std::monostate{}};
  }
  if (c == '(') {
    Advance();
    return DrToken{DrTokenKind::LParen, start_line, start_col,
                   std::monostate{}};
  }
  if (c == ')') {
    Advance();
    return DrToken{DrTokenKind::RParen, start_line, start_col,
                   std::monostate{}};
  }
  if (c == ':') {
    Advance();
    return DrToken{DrTokenKind::Colon, start_line, start_col, std::monostate{}};
  }
  if (c == ',') {
    Advance();
    return DrToken{DrTokenKind::Comma, start_line, start_col, std::monostate{}};
  }
  if (c == ';') {
    Advance();
    return DrToken{DrTokenKind::Semicolon, start_line, start_col,
                   std::monostate{}};
  }
  if (c == '+') {
    Advance();
    return DrToken{DrTokenKind::Plus, start_line, start_col, std::monostate{}};
  }
  if (c == '-') {
    Advance();
    return DrToken{DrTokenKind::Minus, start_line, start_col, std::monostate{}};
  }
  if (c == '*') {
    Advance();
    return DrToken{DrTokenKind::Times, start_line, start_col, std::monostate{}};
  }
  if (c == '/') {
    Advance();
    return DrToken{DrTokenKind::Div, start_line, start_col, std::monostate{}};
  }
  if (c == '^') {
    Advance();
    return DrToken{DrTokenKind::Caret, start_line, start_col, std::monostate{}};
  }
  if (c == '=') {
    Advance();
    if (Current() == '>') {
      Advance();
      return DrToken{DrTokenKind::Implies, start_line, start_col,
                     std::monostate{}};
    }
    return DrToken{DrTokenKind::Eq, start_line, start_col, std::monostate{}};
  }
  if (c == '<') {
    Advance();
    if (Current() == '=') {
      Advance();
      return DrToken{DrTokenKind::Le, start_line, start_col, std::monostate{}};
    }
    return DrToken{DrTokenKind::Lt, start_line, start_col, std::monostate{}};
  }
  if (c == '>') {
    Advance();
    if (Current() == '=') {
      Advance();
      return DrToken{DrTokenKind::Ge, start_line, start_col, std::monostate{}};
    }
    return DrToken{DrTokenKind::Gt, start_line, start_col, std::monostate{}};
  }

  // Number
  if (std::isdigit(c)) {
    return ScanNumber();
  }

  // Identifier or keyword
  if (std::isalpha(c)) {
    return ScanIdentifier();
  }

  throw std::runtime_error("Unexpected character: " + std::string(1, c));
}

DrToken DrLexer::Next() {
  DrToken t;
  if (peeked_) {
    t = std::move(*peeked_);
    peeked_.reset();
  } else {
    t = ScanToken();
  }
  if (debug_) {
    std::cerr << "Token: " << static_cast<int>(t.kind);
    if (std::holds_alternative<std::string>(t.value)) {
      std::cerr << " '" << std::get<std::string>(t.value) << "'";
    }
    std::cerr << " at " << t.line << ":" << t.column << std::endl;
  }
  return t;
}

const DrToken& DrLexer::Peek() {
  if (!peeked_) {
    peeked_ = ScanToken();
  }
  return *peeked_;
}

}  // namespace dreal
