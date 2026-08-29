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

lemma exists_two_cover (T : Finset ℚ) (h : T.card ≤ 2) :
    ∃ a b : ℚ, a ≠ b ∧ ∀ t ∈ T, t = a ∨ t = b := by
  interval_cases hc : T.card
  · exact ⟨0, 1, by norm_num, fun t ht => absurd (Finset.card_eq_zero.mp hc ▸ ht) (by simp)⟩
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
    exact ⟨x, x + 1, by norm_num, fun t ht => Or.inl (by rw [hx] at ht; simpa using ht)⟩
  · obtain ⟨x, y, hxy, hT⟩ := Finset.card_eq_two.mp hc
    exact ⟨x, y, hxy, fun t ht => by rw [hT] at ht; simpa using ht⟩

/-- The affine map sending `a ↦ 0`, `b ↦ 1`. -/
