#pragma once

#include <cstdint>
#include <istream>
#include <optional>
#include <string>
#include <string_view>
#include <variant>
#include <vector>

namespace dreal {

// Token types for SMT2 lexer
enum class TokenKind {
  // End of file
  Eof,
  // Literals
  Int,
  Double,
  String,
  Symbol,
  Keyword,
  // Punctuation
  LParen,
  RParen,
  // Reserved words
  As,
  Let,
  Forall,
  Exists,
  Par,
  Exclamation,
  Underscore,
  // Commands
  Assert,
  CheckSat,
  CheckSatAssuming,
  DeclareConst,
  DeclareFun,
  DeclareSort,
  DefineFun,
  DefineFunRec,
  DefineSort,
  Echo,
  Exit,
  GetAssertions,
  GetAssignment,
  GetInfo,
  GetModel,
  GetOption,
  GetProof,
  GetUnsatAssumptions,
  GetUnsatCore,
  GetValue,
  Pop,
  Push,
  Reset,
  ResetAssertions,
  SetInfo,
  SetLogic,
  SetOption,
  // Punctuation
  LBracket,
  RBracket,
  Comma,
  // Operators
  Plus,
  Minus,
  Times,
  Div,
  Eq,
  Lt,
  Le,
  Gt,
  Ge,
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
  // Boolean
  True,
  False,
  And,
  Or,
  Xor,
  Not,
  Implies,
  Ite,
  // Optimization
  Maximize,
  Minimize,
  // Sorts
  Bool,
  Int_,
  Real,
};

struct SourceLocation {
  int line{1};
  int column{1};
};

struct Token {
  TokenKind kind;
  SourceLocation loc;
  // Value for literals
  std::variant<std::monostate, std::int64_t, double, std::string> value;

  std::int64_t as_int() const { return std::get<std::int64_t>(value); }
  double as_double() const { return std::get<double>(value); }
  const std::string& as_string() const { return std::get<std::string>(value); }
};

class Smt2Lexer {
 public:
  explicit Smt2Lexer(std::istream* input);

  // Get next token
  Token Next();

  // Peek at next token without consuming
  const Token& Peek();

  const std::string& filename() const { return filename_; }
  void set_filename(const std::string& filename) { filename_ = filename; }
  void set_debug(bool v) { debug_ = v; }

 private:
  void Advance();
  char Current() const;
  char LookAhead() const;
  bool AtEnd() const;
  void SkipWhitespaceAndComments();
  Token ScanToken();
  Token ScanNumber();
  Token ScanSymbolOrKeyword();
  Token ScanString();
  Token ScanHashLiteral();
  Token MakeToken(TokenKind kind);
  Token MakeToken(TokenKind kind, std::int64_t value);
  Token MakeToken(TokenKind kind, double value);
  Token MakeToken(TokenKind kind, std::string value);

  std::istream* input_;
  std::string filename_;
  std::string buffer_;
  size_t pos_{0};
  SourceLocation loc_;
  std::optional<Token> peeked_;
  bool debug_{false};
};

}  // namespace dreal
