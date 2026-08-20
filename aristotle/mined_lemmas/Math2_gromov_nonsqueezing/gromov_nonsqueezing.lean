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

theorem gromov_nonsqueezing {n : ℕ} {r R : ℝ} (hR : 0 ≤ R)
    (Φ : V (n + 1) ≃ₗ[ℝ] V (n + 1)) (hΦ : ∀ u v, omg (Φ u) (Φ v) = omg u v)
    (hsub : Φ '' ball (n + 1) r ⊆ cyl n R) : r ≤ R := by
  by_contra hcon
  push_neg at hcon
  -- the inverse map is symplectic too
  have hΦs : ∀ u v, omg (Φ.symm u) (Φ.symm v) = omg u v := by
    intro u v
    have := hΦ (Φ.symm u) (Φ.symm v)
    simpa using this.symm
  set e : V (n + 1) := EuclideanSpace.single ((0 : Fin (n + 1)), (0 : Fin 2)) (1:ℝ) with he
  set f : V (n + 1) := EuclideanSpace.single ((0 : Fin (n + 1)), (1 : Fin 2)) (1:ℝ) with hf
  set a : V (n + 1) := Jm (Φ.symm (-(Jm e))) with ha
  set b : V (n + 1) := Jm (Φ.symm (-(Jm f))) with hb
  -- the coordinate functionals of `Φ` are represented by `a` and `b`
  have repr : ∀ (w z : V (n + 1)), ⟪w, Φ z⟫ = ⟪Jm (Φ.symm (-(Jm w))), z⟫ := by
    intro w z
    have h1 : ⟪w, Φ z⟫ = omg (-(Jm w)) (Φ z) := by
      rw [omg_eq_inner, Jm_neg, Jm_Jm]
      simp
    have h2 : omg (-(Jm w)) (Φ z) = omg (Φ (Φ.symm (-(Jm w)))) (Φ z) := by simp
    rw [h1, h2, hΦ, omg_eq_inner]
  -- `ω(a,b) = 1`
  have homg_ef : omg e f = 1 := by
    simp [omg, he, hf, EuclideanSpace.single_apply]
  have homgab : omg a b = 1 := by
    rw [ha, hb, omg_Jm_Jm, hΦs, omg_neg_neg, omg_Jm_Jm, homg_ef]
  have hgram : 1 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
    have hg := gram_bound a (Jm a) b (inner_Jm_self a) (norm_Jm a)
    rw [← omg_eq_inner, homgab] at hg
    linarith
  obtain ⟨w, hw1, hw2⟩ := exists_unit_of_gram a b hgram
  -- the point `R • w` lies in the ball, hence its image lies in the cylinder
  have hmem : Φ (R • w) ∈ cyl n R := by
    refine hsub ⟨R • w, ?_, rfl⟩
    simp only [ball, Set.mem_setOf_eq, norm_smul, hw1, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hR]
    exact hcon
  have hc0 : (Φ (R • w)).ofLp ((0 : Fin (n + 1)), (0 : Fin 2)) = R * ⟪a, w⟫ := by
    have := repr e (R • w)
    rw [he] at this
    rw [EuclideanSpace.inner_single_left] at this
    simp only [map_one, one_mul] at this
    rw [this, ← ha, real_inner_smul_right]
  have hc1 : (Φ (R • w)).ofLp ((0 : Fin (n + 1)), (1 : Fin 2)) = R * ⟪b, w⟫ := by
    have := repr f (R • w)
    rw [hf] at this
    rw [EuclideanSpace.inner_single_left] at this
    simp only [map_one, one_mul] at this
    rw [this, ← hb, real_inner_smul_right]
  simp only [cyl, Set.mem_setOf_eq, hc0, hc1, mul_pow] at hmem
  nlinarith [sq_nonneg R, hmem, hw2]

/-- Sharpness (and non-vacuity) of the previous theorem: whenever `r ≤ R`, the identity
linear symplectomorphism does map the ball of radius `r` into the cylinder of radius `R`. -/
