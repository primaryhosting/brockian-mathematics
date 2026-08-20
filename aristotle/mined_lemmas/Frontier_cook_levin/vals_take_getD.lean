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

theorem vals_take_getD (p : List Gate) (x : ℕ → Bool) {j : ℕ} (hj : j ≤ p.length) (k : ℕ) :
    (vals (p.take j) x).getD k false = if k < j then (vals p x).getD k false else false := by
  have hlen : (vals (p.take j) x).length = j := by
    rw [vals_length, List.length_take]; omega
  by_cases hk : k < j
  · rw [if_pos hk]
    exact (getD_of_prefix (vals_take_prefix p x j) (by omega)).symm
  · rw [if_neg hk]
    exact List.getD_eq_default _ false (by omega)

