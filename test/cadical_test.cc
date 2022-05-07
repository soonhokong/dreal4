/*
   Copyright 2022 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
#include "./cadical.hpp"

#include <iostream>

#include <gtest/gtest.h>

int main() {
  // The following example is based on the example in cadical.hpp.
  // See https://github.com/arminbiere/cadical/blob/master/src/cadical.hpp
  CaDiCaL::Solver* solver = new CaDiCaL::Solver;

  // ------------------------------------------------------------------
  // Encode Problem and check without assumptions.

  enum { TIE = 1, SHIRT = 2 };

  solver->add(-TIE), solver->add(SHIRT), solver->add(0);
  solver->add(TIE), solver->add(SHIRT), solver->add(0);
  solver->add(-TIE), solver->add(-SHIRT), solver->add(0);

  int res = solver->solve();  // Solve instance.
  EXPECT_TRUE(res == 10);     // Check it is 'SATISFIABLE'.

  res = solver->val(TIE);  // Obtain assignment of 'TIE'.
  EXPECT_TRUE(res < 0);    // Check 'TIE' assigned to 'false'.

  res = solver->val(SHIRT);  // Obtain assignment of 'SHIRT'.
  EXPECT_TRUE(res > 0);      // Check 'SHIRT' assigned to 'true'.

  // ------------------------------------------------------------------
  // Incrementally solve again under one assumption.

  solver->assume(TIE);  // Now force 'TIE' to true.

  res = solver->solve();   // Solve again incrementally.
  EXPECT_TRUE(res == 20);  // Check it is 'UNSATISFIABLE'.

  res = solver->failed(TIE);  // Check 'TIE' responsible.
  EXPECT_TRUE(res);           // Yes, 'TIE' in core.

  res = solver->failed(SHIRT);  // Check 'SHIRT' responsible.
  EXPECT_TRUE(!res);            // No, 'SHIRT' not in core.

  // ------------------------------------------------------------------
  // Incrementally solve once more under another assumption.

  solver->assume(-SHIRT);  // Now force 'SHIRT' to false.

  res = solver->solve();   // Solve again incrementally.
  EXPECT_TRUE(res == 20);  // Check it is 'UNSATISFIABLE'.

  res = solver->failed(TIE);  // Check 'TIE' responsible.
  EXPECT_TRUE(!res);          // No, 'TIE' not in core.

  res = solver->failed(-SHIRT);  // Check '!SHIRT' responsible.
  EXPECT_TRUE(res);              // Yes, '!SHIRT' in core.

  // ------------------------------------------------------------------

  delete solver;

  return 0;
}
