# Boolean Literals in Learned Clauses

This document explains a bug fix in dReal's SMT solver related to how learned clauses are constructed (Issue #324).

## Background: SMT Solving

An SMT (Satisfiability Modulo Theories) solver combines:
1. A **SAT solver** that handles Boolean logic
2. A **theory solver** that handles domain-specific constraints (e.g., arithmetic over real numbers)

The basic algorithm (DPLL(T)) works as follows:
1. SAT solver proposes a Boolean assignment
2. Theory solver checks if the assignment is consistent with the theory
3. If inconsistent, the theory solver returns an **explanation** (the subset of constraints that caused the conflict)
4. A **learned clause** is added to prevent the SAT solver from trying the same conflicting combination again
5. Repeat until SAT (found a model) or UNSAT (no valid assignment exists)

## The Problem

### How Theory Literals Become SAT Variables

When dReal processes a formula, theory constraints like `(x > 5)` are converted to Boolean variables by the **predicate abstractor**. For example:
- `(x > 5)` → `b((x > 5))` (SAT variable 7)
- `(x <= 10)` → `b((x <= 10))` (SAT variable 8)

The predicate abstractor maintains a map from formulas to Boolean variables.

### The Bug

When the SAT solver assigns a theory literal to `false`, the assertion passed to the theory solver is the **negation** of the original formula:

```cpp
assertions.push_back(p.second ? sat_solver->theory_literal(p.first)
                              : !sat_solver->theory_literal(p.first));
```

For example, if `b((x <= 10))` is assigned `false`, the assertion becomes `!(x <= 10)`.

When the theory solver returns an explanation containing `!(x <= 10)`, the old code tried to convert this back to a SAT variable:

```cpp
AddLiteral(!predicate_abstractor_.Convert(f));  // f = !(x <= 10)
```

The problem: **the predicate abstractor might not correctly map `!(x <= 10)` back to the original SAT variable**. The map contains `(x <= 10)`, not `!(x <= 10)`. While the code handles negation, subtle differences in formula representation could cause mismatches.

When the mapping fails, the learned clause becomes ineffective, leading to:
- Different results depending on the order of disjuncts (`(or A B)` vs `(or B A)`)
- The solver might return UNSAT for satisfiable formulas

## The Solution

Instead of converting explanation formulas back through the predicate abstractor, we now directly match explanation formulas against the theory literals from the SAT model:

```cpp
vector<pair<Variable, bool>> theory_literals_in_explanation;
for (const auto& p : theory_model) {
  const Formula& lit = sat_solver->theory_literal(p.first);
  const Formula lit_used = p.second ? lit : !lit;
  if (explanation.count(lit_used) > 0) {
    theory_literals_in_explanation.push_back(p);
  }
}
// Also include positive Boolean literals for robustness
for (const auto& p : boolean_model) {
  if (p.second) {
    theory_literals_in_explanation.push_back(p);
  }
}
sat_solver->AddLearnedClause(theory_literals_in_explanation);
```

This approach:
1. Uses the exact same formula objects that were passed to the theory solver
2. Directly uses the SAT variables from the model (no conversion needed)
3. Includes positive Boolean literals as an additional safeguard

## Summary

The fix ensures learned clauses correctly reference the SAT variables that caused the conflict, by matching explanation formulas directly against the theory model rather than relying on formula-to-variable conversion.
