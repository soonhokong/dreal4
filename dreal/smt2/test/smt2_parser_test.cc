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
#include "dreal/smt2/smt2_parser.h"

#include <sstream>

#include <gtest/gtest.h>

namespace dreal {
namespace {

TEST(Smt2ParserTest, BasicSat) {
  std::istringstream input(R"(
    (set-logic QF_NRA)
    (declare-const x Real)
    (assert (and (<= 0 x) (<= x 10)))
    (check-sat)
    (exit)
  )");
  Smt2Parser parser(&input);
  parser.Parse();
}

TEST(Smt2ParserTest, Arithmetic) {
  std::istringstream input(R"(
    (set-logic QF_NRA)
    (declare-const x Real)
    (declare-const y Real)
    (assert (= (+ x y) 10))
    (assert (= (* x y) 21))
    (check-sat)
    (exit)
  )");
  Smt2Parser parser(&input);
  parser.Parse();
}

TEST(Smt2ParserTest, Transcendental) {
  std::istringstream input(R"(
    (set-logic QF_NRA)
    (declare-const x Real)
    (assert (= (sin x) 0.5))
    (check-sat)
    (exit)
  )");
  Smt2Parser parser(&input);
  parser.Parse();
}

TEST(Smt2ParserTest, Let) {
  std::istringstream input(R"(
    (set-logic QF_NRA)
    (declare-const x Real)
    (assert (let ((y (+ x 1))) (> y 0)))
    (check-sat)
    (exit)
  )");
  Smt2Parser parser(&input);
  parser.Parse();
}

TEST(Smt2ParserTest, DefineFun) {
  std::istringstream input(R"(
    (set-logic QF_NRA)
    (declare-const x Real)
    (define-fun square ((a Real)) Real (* a a))
    (assert (= (square x) 4))
    (check-sat)
    (exit)
  )");
  Smt2Parser parser(&input);
  parser.Parse();
}

}  // namespace
}  // namespace dreal
