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


lemma isSimon_adv (Q : Finset (BV n)) (s : BV n) (hs : s ≠ 0) : IsSimon (adv Q s) s := by
  refine ⟨hs, fun x z => ⟨?_, ?_⟩⟩
  · intro heq
    rcases adv_mem Q s x with hx | hx <;> rcases adv_mem Q s z with hz | hz
    · exact Or.inl (by rw [← hz, ← heq, hx])
    · have hxz : x = z + s := by rw [← hx, heq, hz]
      exact Or.inr (by rw [hxz, BV.add_add_cancel])
    · have hxz : x + s = z := by rw [← hx, heq, hz]
      exact Or.inr hxz.symm
    · have hxz : x + s = z + s := by rw [← hx, heq, hz]
      exact Or.inl (add_right_cancel hxz).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (adv_shift Q s x).symm

