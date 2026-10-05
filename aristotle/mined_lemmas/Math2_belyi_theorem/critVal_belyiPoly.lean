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

lemma critVal_belyiPoly (a b : ℕ) : critVal (belyiPoly a b) ⊆ ({0, 1} : Set ℂ) := by
  rintro v ⟨w, hw, rfl⟩
  rw [derivative_belyiPoly] at hw
  simp only [map_mul, map_sub, map_pow, map_one, aeval_C, aeval_X, mul_eq_zero,
    sub_eq_zero, eq_ratCast] at hw
  have hc : ((belyiC a b : ℚ) : ℂ) ≠ 0 := (Rat.cast_ne_zero (α := ℂ)).mpr (belyiC_ne_zero a b)
  rcases hw with hc' | hw
  · exact absurd hc' hc
  rcases hw with hw | hw
  · have hw0 : w = 0 := (pow_eq_zero_iff'.mp hw).1
    subst hw0
    left
    simp [belyiPoly]
  rcases hw with hw | hw
  · have hw1 : w = 1 := by
      have h := (pow_eq_zero_iff'.mp hw).1
      linear_combination -h
    subst hw1
    left
    simp [belyiPoly]
  · have hden : ((a : ℂ) + b + 2) ≠ 0 := by
      intro hcon
      have h2 : ((a : ℂ) + b + 2).re = 0 := by rw [hcon]; simp
      simp only [Complex.add_re, Complex.natCast_re, Complex.re_ofNat] at h2
      have : (0 : ℝ) < (a : ℝ) + b + 2 := by positivity
      linarith
    have hwv : w = ((belyiPt a b : ℚ) : ℂ) := by
      unfold belyiPt
      push_cast at hw ⊢
      field_simp
      linear_combination -hw
    subst hwv
    right
    rw [aeval_ratCast, belyiPoly_eval_pt]
    norm_num

/-- Every rational number in `(0,1)` is of the form `belyiPt a b`. -/
