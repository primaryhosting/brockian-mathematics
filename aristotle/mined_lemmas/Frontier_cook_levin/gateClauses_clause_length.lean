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

theorem gateClauses_clause_length (j : ℕ) (g : Gate) (c : Clause) (hc : c ∈ gateClauses j g) :
    c.length ≤ 3 := by
  cases g with
  | inp i => simp [gateClauses] at hc; rcases hc with h | h <;> subst h <;> simp
  | cst b => cases b <;> (simp [gateClauses] at hc; subst hc; simp)
  | neg k => simp [gateClauses] at hc; rcases hc with h | h <;> subst h <;> simp
  | conj k l => simp [gateClauses] at hc; rcases hc with h | h | h <;> subst h <;> simp
  | disj k l => simp [gateClauses] at hc; rcases hc with h | h | h <;> subst h <;> simp

