/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- repeated as a module docstring immediately after the import.)

import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Bit vectors -/

/-- `n`-bit strings, as a vector space over `ZMod 2`. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

variable {n : ℕ}


lemma adv_mem (Q : Finset (BV n)) (s x : BV n) :
    adv Q s x = x ∨ adv Q s x = x + s := by
  rcases rep_mem s x with hr | hr <;> rcases adv_mem_rep Q s x with h | h
  · exact Or.inl (by rw [h, hr])
  · exact Or.inr (by rw [h, hr])
  · exact Or.inr (by rw [h, hr])
  · exact Or.inl (by rw [h, hr, BV.add_add_cancel])

