/*
   Copyright 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
#include "dreal/solver/brancher_gnn.h"

#include <vector>

#include <gtest/gtest.h>

namespace dreal {
namespace {

using std::vector;

GTEST_TEST(BrancherGnn, ExtractPatternTest) {
  const Variable ITE0{"ITE0"};
  const Variable ITE1{"ITE1"};
  const Variable ITE2{"ITE2"};
  const Variable ITE3{"ITE3"};
  const Variable A2B{"A2B"};

  const Formula f1{ITE3 == 3.14 * (-3.15 + (A2B / 3.0))};

  const BranchTheoryLiteralPattern p1{ExtractPattern(f1)};

  EXPECT_EQ(p1.pattern, "(ITE3==({}*({}+(A2B/{}))))");
  EXPECT_EQ(p1.parameters, (vector<double>{3.14, -3.15, 3.0}));
}

}  // namespace
}  // namespace dreal
