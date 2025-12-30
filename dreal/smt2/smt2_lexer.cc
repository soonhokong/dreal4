#include "dreal/smt2/smt2_lexer.h"

#include <cctype>
#include <cstdlib>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <unordered_map>

namespace dreal {

namespace {

const std::unordered_map<std::string, TokenKind> kKeywords = {
    // Reserved words
    {"as", TokenKind::As},
    {"let", TokenKind::Let},
    {"forall", TokenKind::Forall},
    {"exists", TokenKind::Exists},
    {"par", TokenKind::Par},
    {"_", TokenKind::Underscore},
    // Commands
    {"assert", TokenKind::Assert},
    {"check-sat", TokenKind::CheckSat},
    {"check-sat-assuming", TokenKind::CheckSatAssuming},
    {"declare-const", TokenKind::DeclareConst},
    {"declare-fun", TokenKind::DeclareFun},
    {"declare-sort", TokenKind::DeclareSort},
    {"define-fun", TokenKind::DefineFun},
    {"define-fun-rec", TokenKind::DefineFunRec},
    {"define-sort", TokenKind::DefineSort},
    {"echo", TokenKind::Echo},
    {"exit", TokenKind::Exit},
    {"get-assertions", TokenKind::GetAssertions},
    {"get-assignment", TokenKind::GetAssignment},
    {"get-info", TokenKind::GetInfo},
    {"get-model", TokenKind::GetModel},
    {"get-option", TokenKind::GetOption},
    {"get-proof", TokenKind::GetProof},
    {"get-unsat-assumptions", TokenKind::GetUnsatAssumptions},
    {"get-unsat-core", TokenKind::GetUnsatCore},
    {"get-value", TokenKind::GetValue},
    {"pop", TokenKind::Pop},
    {"push", TokenKind::Push},
    {"reset", TokenKind::Reset},
    {"reset-assertions", TokenKind::ResetAssertions},
    {"set-info", TokenKind::SetInfo},
    {"set-logic", TokenKind::SetLogic},
    {"set-option", TokenKind::SetOption},
    // Operators
    {"+", TokenKind::Plus},
    {"-", TokenKind::Minus},
    {"*", TokenKind::Times},
    {"/", TokenKind::Div},
    {"=", TokenKind::Eq},
    {"<", TokenKind::Lt},
    {"<=", TokenKind::Le},
    {">", TokenKind::Gt},
    {">=", TokenKind::Ge},
    {"=>", TokenKind::Implies},
    // Functions
    {"exp", TokenKind::Exp},
    {"log", TokenKind::Log},
    {"abs", TokenKind::Abs},
    {"sin", TokenKind::Sin},
    {"cos", TokenKind::Cos},
    {"tan", TokenKind::Tan},
    {"asin", TokenKind::Asin},
    {"arcsin", TokenKind::Asin},
    {"acos", TokenKind::Acos},
    {"arccos", TokenKind::Acos},
    {"atan", TokenKind::Atan},
    {"arctan", TokenKind::Atan},
    {"atan2", TokenKind::Atan2},
    {"arctan2", TokenKind::Atan2},
    {"sinh", TokenKind::Sinh},
    {"cosh", TokenKind::Cosh},
    {"tanh", TokenKind::Tanh},
    {"min", TokenKind::Min},
    {"max", TokenKind::Max},
    {"sqrt", TokenKind::Sqrt},
    {"pow", TokenKind::Pow},
    {"^", TokenKind::Pow},
    // Boolean
    {"true", TokenKind::True},
    {"false", TokenKind::False},
    {"and", TokenKind::And},
    {"or", TokenKind::Or},
    {"xor", TokenKind::Xor},
    {"not", TokenKind::Not},
    {"ite", TokenKind::Ite},
    // Optimization
    {"maximize", TokenKind::Maximize},
    {"minimize", TokenKind::Minimize},
    // Sorts
    {"Bool", TokenKind::Bool},
    {"Int", TokenKind::Int_},
    {"Real", TokenKind::Real},
};

bool IsSymbolChar(char c) {
  return std::isalnum(c) || c == '+' || c == '-' || c == '/' || c == '*' ||
         c == '=' || c == '%' || c == '?' || c == '!' || c == '.' || c == '$' ||
         c == '_' || c == '~' || c == '&' || c == '^' || c == '<' || c == '>' ||
         c == '@';
}

}  // namespace

Smt2Lexer::Smt2Lexer(std::istream* input) : input_(input) {
  // Read entire input into buffer for simpler parsing
  std::ostringstream ss;
  ss << input_->rdbuf();
  buffer_ = ss.str();
}

void Smt2Lexer::Advance() {
  if (pos_ < buffer_.size()) {
    if (buffer_[pos_] == '\n') {
      loc_.line++;
      loc_.column = 1;
    } else {
      loc_.column++;
    }
    pos_++;
  }
}

char Smt2Lexer::Current() const {
  return pos_ < buffer_.size() ? buffer_[pos_] : '\0';
}

char Smt2Lexer::LookAhead() const {
  return pos_ + 1 < buffer_.size() ? buffer_[pos_ + 1] : '\0';
}

bool Smt2Lexer::AtEnd() const { return pos_ >= buffer_.size(); }

void Smt2Lexer::SkipWhitespaceAndComments() {
  while (!AtEnd()) {
    char c = Current();
    if (std::isspace(c)) {
      Advance();
    } else if (c == ';') {
      // Skip comment until end of line
      while (!AtEnd() && Current() != '\n') {
        Advance();
      }
    } else {
      break;
    }
  }
}

Token Smt2Lexer::MakeToken(TokenKind kind) {
  return Token{kind, loc_, std::monostate{}};
}

Token Smt2Lexer::MakeToken(TokenKind kind, std::int64_t value) {
  return Token{kind, loc_, value};
}

Token Smt2Lexer::MakeToken(TokenKind kind, double value) {
  return Token{kind, loc_, value};
}

Token Smt2Lexer::MakeToken(TokenKind kind, std::string value) {
  return Token{kind, loc_, std::move(value)};
}

Token Smt2Lexer::ScanNumber() {
  SourceLocation start_loc = loc_;
  size_t start = pos_;
  bool is_float = false;

  // Optional sign
  if (Current() == '+' || Current() == '-') {
    Advance();
  }

  // Check for hex float: 0x...
  if (Current() == '0' && LookAhead() == 'x') {
    Advance();  // consume '0'
    Advance();  // consume 'x'
    // Hex digits
    while (!AtEnd() && (std::isxdigit(Current()) || Current() == '.')) {
      if (Current() == '.') is_float = true;
      Advance();
    }
    // Exponent part (p or P)
    if (Current() == 'p' || Current() == 'P') {
      is_float = true;
      Advance();
      if (Current() == '+' || Current() == '-') {
        Advance();
      }
      while (!AtEnd() && std::isdigit(Current())) {
        Advance();
      }
    }
    std::string num_str = buffer_.substr(start, pos_ - start);
    return Token{TokenKind::Double, start_loc, num_str};
  }

  // Integer part
  while (!AtEnd() && std::isdigit(Current())) {
    Advance();
  }

  // Decimal part
  if (Current() == '.' && std::isdigit(LookAhead())) {
    is_float = true;
    Advance();  // consume '.'
    while (!AtEnd() && std::isdigit(Current())) {
      Advance();
    }
  }

  // Exponent part
  if (Current() == 'e' || Current() == 'E') {
    is_float = true;
    Advance();
    if (Current() == '+' || Current() == '-') {
      Advance();
    }
    while (!AtEnd() && std::isdigit(Current())) {
      Advance();
    }
  }

  std::string num_str = buffer_.substr(start, pos_ - start);

  if (is_float) {
    return Token{TokenKind::Double, start_loc, num_str};
  } else {
    try {
      std::int64_t val = std::stoll(num_str);
      return Token{TokenKind::Int, start_loc, val};
    } catch (...) {
      // Fall back to double for very large integers
      return Token{TokenKind::Double, start_loc, num_str};
    }
  }
}

Token Smt2Lexer::ScanSymbolOrKeyword() {
  SourceLocation start_loc = loc_;
  size_t start = pos_;
  bool is_keyword = (Current() == ':');

  if (is_keyword) {
    Advance();  // consume ':'
  }

  while (!AtEnd() && IsSymbolChar(Current())) {
    Advance();
  }

  std::string text = buffer_.substr(start, pos_ - start);

  if (is_keyword) {
    return Token{TokenKind::Keyword, start_loc, text};
  }

  // Check if it's a reserved word
  auto it = kKeywords.find(text);
  if (it != kKeywords.end()) {
    return Token{it->second, start_loc, std::monostate{}};
  }

  return Token{TokenKind::Symbol, start_loc, text};
}

Token Smt2Lexer::ScanString() {
  SourceLocation start_loc = loc_;
  Advance();  // consume opening '"'

  std::string result;
  while (!AtEnd() && Current() != '"') {
    if (Current() == '\\' && LookAhead() == '"') {
      Advance();  // skip backslash
      result += '"';
      Advance();
    } else {
      result += Current();
      Advance();
    }
  }

  if (AtEnd()) {
    throw std::runtime_error("Unterminated string literal");
  }

  Advance();  // consume closing '"'
  return Token{TokenKind::String, start_loc, result};
}

Token Smt2Lexer::ScanToken() {
  SkipWhitespaceAndComments();

  if (AtEnd()) {
    return MakeToken(TokenKind::Eof);
  }

  SourceLocation start_loc = loc_;
  char c = Current();

  // Parentheses
  if (c == '(') {
    Advance();
    return Token{TokenKind::LParen, start_loc, std::monostate{}};
  }
  if (c == ')') {
    Advance();
    return Token{TokenKind::RParen, start_loc, std::monostate{}};
  }

  // String literal
  if (c == '"') {
    return ScanString();
  }

  // Quoted symbol |...|
  if (c == '|') {
    Advance();  // consume '|'
    size_t start = pos_;
    while (!AtEnd() && Current() != '|') {
      Advance();
    }
    std::string text = buffer_.substr(start, pos_ - start);
    if (!AtEnd()) {
      Advance();  // consume closing '|'
    }
    return Token{TokenKind::Symbol, start_loc, text};
  }

  // Number (starts with digit or sign followed by digit)
  if (std::isdigit(c) ||
      ((c == '+' || c == '-') && std::isdigit(LookAhead()))) {
    return ScanNumber();
  }

  // Keyword (starts with ':')
  if (c == ':') {
    return ScanSymbolOrKeyword();
  }

  // Symbol or reserved word
  if (IsSymbolChar(c)) {
    return ScanSymbolOrKeyword();
  }

  // Brackets and comma (for interval syntax)
  if (c == '[') {
    Advance();
    return Token{TokenKind::LBracket, start_loc, std::monostate{}};
  }
  if (c == ']') {
    Advance();
    return Token{TokenKind::RBracket, start_loc, std::monostate{}};
  }
  if (c == ',') {
    Advance();
    return Token{TokenKind::Comma, start_loc, std::monostate{}};
  }

  // Exclamation mark (annotation)
  if (c == '!') {
    Advance();
    return Token{TokenKind::Exclamation, start_loc, std::monostate{}};
  }

  throw std::runtime_error(std::string("Unexpected character: ") + c);
}

Token Smt2Lexer::Next() {
  Token t;
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
    std::cerr << " at " << t.loc.line << ":" << t.loc.column << std::endl;
  }
  return t;
}

const Token& Smt2Lexer::Peek() {
  if (!peeked_) {
    peeked_ = ScanToken();
  }
  return *peeked_;
}

}  // namespace dreal
