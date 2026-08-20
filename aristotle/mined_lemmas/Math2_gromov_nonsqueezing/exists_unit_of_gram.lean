/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

/-! ## The standard symplectic vector space `ℝ^{2n}`

We model `ℝ^{2n}` as the Euclidean space indexed by `Fin n × Fin 2`, where for each
`i : Fin n` the coordinate `(i,0)` is the position `x i` and `(i,1)` is the momentum `y i`.
-/

/-- The standard `2n`-dimensional Euclidean/symplectic vector space. -/
abbrev V (n : ℕ) : Type := EuclideanSpace ℝ (Fin n × Fin 2)

/-- The standard symplectic form `ω(u,v) = ∑ i, (u_{x i} v_{y i} - u_{y i} v_{x i})`. -/

lemma exists_unit_of_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (h : 1 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2) :
    ∃ w : E, ‖w‖ = 1 ∧ 1 ≤ ⟪a, w⟫ ^ 2 + ⟪b, w⟫ ^ 2 := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h
    linarith [h]
  have hA : (0:ℝ) < ‖a‖ ^ 2 := by positivity
  rcases le_or_gt 1 (‖a‖ ^ 2) with hcase | hcase
  · refine ⟨‖a‖⁻¹ • a, ?_, ?_⟩
    · rw [norm_smul]
      simp [norm_ne_zero_iff.mpr ha]
    · have hval : ⟪a, ‖a‖⁻¹ • a⟫ = ‖a‖ := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      rw [hval]
      nlinarith [sq_nonneg ⟪b, ‖a‖⁻¹ • a⟫]
  · set q : E := b - (⟪a, b⟫ / ‖a‖ ^ 2) • a with hq
    have haa : ⟪a, a⟫ = ‖a‖ ^ 2 := real_inner_self_eq_norm_sq a
    have hbb : ⟪b, b⟫ = ‖b‖ ^ 2 := real_inner_self_eq_norm_sq b
    have haq : ⟪a, q⟫ = 0 := by
      simp only [hq, inner_sub_right, real_inner_smul_right, haa]
      field_simp
      ring
    have hqq : ⟪q, q⟫ = (‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2) / ‖a‖ ^ 2 := by
      simp only [hq, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        haa, hbb, real_inner_comm b a]
      field_simp
      ring
    have hbq : ⟪b, q⟫ = ⟪q, q⟫ := by
      have hexp : ⟪q, q⟫ = ⟪b, q⟫ - (⟪a, b⟫ / ‖a‖ ^ 2) * ⟪a, q⟫ := by
        rw [hq]
        simp only [inner_sub_left, real_inner_smul_left]
      rw [hexp, haq]
      ring
    have hqn : ‖q‖ ^ 2 = ⟪q, q⟫ := (real_inner_self_eq_norm_sq q).symm
    have hqpos : 1 < ‖q‖ ^ 2 := by
      rw [hqn, hqq, lt_div_iff₀ hA]
      nlinarith
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0] at hqpos
      simp at hqpos
      linarith
    refine ⟨‖q‖⁻¹ • q, ?_, ?_⟩
    · rw [norm_smul]
      simp [norm_ne_zero_iff.mpr hq0]
    · have hval : ⟪b, ‖q‖⁻¹ • q⟫ = ‖q‖ := by
        rw [real_inner_smul_right, hbq, ← hqn]
        field_simp
      rw [hval]
      nlinarith [sq_nonneg ⟪a, ‖q‖⁻¹ • q⟫]

/-! ## Gromov nonsqueezing (linear case) -/

/-- Gromov's nonsqueezing theorem for linear symplectomorphisms: a linear
symplectomorphism of the standard symplectic vector space `ℝ^{2(n+1)}` cannot map the
open ball of radius `r` into the open symplectic cylinder of radius `R` unless `r ≤ R`. -/
