import Mathlib
/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000

namespace Math2

open Polynomial IntermediateField

noncomputable section

/-! ## Basic notions -/

/-- The set of critical values in `ℂ` of a polynomial with rational coefficients.
Viewing `f ∈ ℚ[X]` as a morphism `ℙ¹ → ℙ¹`, these are the finite branch points of `f`. -/

lemma critVal_eq_empty_of_derivative_const (f : ℚ[X]) (u : ℚ) (hu : u ≠ 0)
    (h : derivative f = C u) : critVal f = ∅ := by
  ext v
  simp only [critVal, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨w, hw, rfl⟩
  rw [h] at hw
  simp only [aeval_C, eq_ratCast, Rat.cast_eq_zero] at hw
  exact hu hw

