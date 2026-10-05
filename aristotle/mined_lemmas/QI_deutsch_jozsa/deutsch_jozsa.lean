import Mathlib

/-!
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

/-! ## Setup

We model the Deutsch–Jozsa algorithm on `n` query bits.  A computational basis
state is an element of `Fin n → Bool`, and a (pure) state of the query register
is a function `(Fin n → Bool) → ℂ` of amplitudes. -/

variable {n : ℕ}

/-- The sign `(-1)^b` attached to a Boolean value. -/

theorem deutsch_jozsa (f : (Fin n → Bool) → Bool) (hf : IsConstant f ∨ IsBalanced f) :
    (djZeroProb f = 1 ↔ IsConstant f) ∧ (djZeroProb f = 0 ↔ IsBalanced f) := by
  have hconst : IsConstant f → djZeroProb f = 1 := by
    intro hc
    rw [djZeroProb, djFinal_zero_of_constant f hc, one_pow]
  have hbal : IsBalanced f → djZeroProb f = 0 := by
    intro hb
    rw [djZeroProb, djFinal_zero_of_balanced f hb]
    norm_num
  refine ⟨⟨fun h => ?_, hconst⟩, ⟨fun h => ?_, hbal⟩⟩
  · rcases hf with hc | hb
    · exact hc
    · rw [hbal hb] at h
      norm_num at h
  · rcases hf with hc | hb
    · rw [hconst hc] at h
      norm_num at h
    · exact hb

end QI

