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

def gateClauses (j : ℕ) : Gate → CNF
  | .inp i => [[(gvar j, false), (xvar i, true)], [(gvar j, true), (xvar i, false)]]
  | .cst b => if b then [[(gvar j, true)]] else [[(gvar j, false)]]
  | .neg k => [[(gvar j, false), refLit j k false], [(gvar j, true), refLit j k true]]
  | .conj k l =>
      [[(gvar j, false), refLit j k true], [(gvar j, false), refLit j l true],
       [(gvar j, true), refLit j k false, refLit j l false]]
  | .disj k l =>
      [[(gvar j, true), refLit j k false], [(gvar j, true), refLit j l false],
       [(gvar j, false), refLit j k true, refLit j l true]]

/-- The Tseitin CNF encoding of a straight-line program: it is satisfiable iff
the program outputs `true` on some input. -/
