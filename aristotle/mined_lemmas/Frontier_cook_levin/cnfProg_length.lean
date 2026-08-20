/-
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cook Levin
Category: Frontier — Moonshot
Target: Frontier.cook_levin
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

/-! ## CNF formulas -/

/-- A literal: a variable index together with a sign (`true` = positive). -/
abbrev Lit : Type := ℕ × Bool

/-- A clause is a disjunction of literals. -/
abbrev Clause : Type := List Lit

/-- A CNF formula is a conjunction of clauses. -/
abbrev CNF : Type := List Clause

/-- Value of a literal under an assignment. -/

theorem cnfProg_length (f : CNF) :
    (cnfProg f).length ≤ 4 * (f.length + (f.map List.length).sum) + 1 := by
  have := cnfProg_length_aux f
  omega

/-! ## Cook–Levin -/

/-- **Cook–Levin theorem** (Boolean-circuit formulation).

The first conjunct is NP-*membership* of CNF-SAT: for every CNF formula `f`
there is a straight-line Boolean program of size linear in `f` which, given an
assignment, checks whether the assignment satisfies `f`; so satisfiability is
witnessed by an assignment that can be verified efficiently.

The second conjunct is NP-*hardness* of CNF-SAT: for every language `L` that
admits a polynomial-size verifier (an `NPCert`) there is a many-one reduction
`f` from `L` to CNF-SAT producing formulas of polynomial size with clauses of
at most three literals (so in fact a reduction to 3-SAT). -/
