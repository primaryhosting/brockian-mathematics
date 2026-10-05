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

lemma degQ_eq_one_iff (z : ℂ) : degQ z = 1 ↔ ∃ q : ℚ, (q : ℂ) = z := by
  rw [degQ, minpoly.natDegree_eq_one_iff]
  constructor
  · rintro ⟨q, hq⟩; exact ⟨q, by simpa using hq⟩
  · rintro ⟨q, hq⟩; exact ⟨q, by simpa using hq⟩

