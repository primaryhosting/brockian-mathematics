import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
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
set_option pp.piBinderTypes true

set_option grind.warning false

open Ordinal
open scoped NaturalOps

namespace Frontier

/-!
## Part 1: `ω ^ c` is principal for natural (Hessenberg) addition

Mathlib knows that `ω ^ c` is principal for ordinary ordinal addition, but not for the
natural sum `♯`.  We prove this here, since the ordinal assignment used for the hydra
game relies on it.
-/

/-- Every ordinal below `ω ^ d * ω` can be written as `ω ^ d * m + r` with `m` a natural
number and `r < ω ^ d`. -/

theorem decomp_cases (d : Ordinal) (m m' : ℕ) (r r' : Ordinal) (hr : r < ω ^ d)
    (h : ω ^ d * (m' : Ordinal) + r' < ω ^ d * (m : Ordinal) + r) :
    m' < m ∨ (m' = m ∧ r' < r) := by
  rcases lt_trichotomy m' m with hm | hm | hm
  · exact Or.inl hm
  · subst hm
    exact Or.inr ⟨rfl, (add_lt_add_iff_left _).1 h⟩
  · exfalso
    have h1 : ω ^ d * (m : Ordinal) + r < ω ^ d * ((m : Ordinal) + 1) := by
      rw [mul_add, mul_one]; exact (add_lt_add_iff_left _).2 hr
    have h2 : ω ^ d * ((m : Ordinal) + 1) ≤ ω ^ d * (m' : Ordinal) := by
      exact mul_le_mul_right (by exact_mod_cast Nat.succ_le_of_lt hm) _
    have h3 : ω ^ d * (m' : Ordinal) ≤ ω ^ d * (m' : Ordinal) + r' := le_self_add
    exact absurd h (not_lt.2 ((h1.trans_le h2).le.trans h3))

/-- The key merge estimate: natural addition of two ordinals written in base `ω ^ d`
adds the base-`ω ^ d` digits. -/
