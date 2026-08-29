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

lemma belyiPoly_natDegree_pos (a b : ℕ) : 0 < (belyiPoly a b).natDegree := by
  rcases Nat.eq_zero_or_pos (belyiPoly a b).natDegree with hh | hh
  · exfalso
    have hc := Polynomial.eq_C_of_natDegree_eq_zero hh
    have h0 := belyiPoly_eval_zero a b
    have h1 := belyiPoly_eval_pt a b
    rw [hc] at h0 h1
    simp only [eval_C] at h0 h1
    rw [h0] at h1
    exact absurd h1 (by norm_num)
  · exact hh

