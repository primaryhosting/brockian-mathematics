/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Set Metric

/-- A **quadratic-like map** in the sense of Douady–Hubbard: a holomorphic map
`f : U → V` between bounded connected open subsets of `ℂ` with `closure U ⊆ V`,
which is a branched covering of degree two (every fibre over `V` is a non-empty set of
at most two points, and some fibre has exactly two points). -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the large domain -/
  V : Set ℂ
  /-- the map -/
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isPreconnected_U : IsPreconnected U
  isPreconnected_V : IsPreconnected V
  isBounded_V : Bornology.IsBounded V
  closure_U_subset_V : closure U ⊆ V
  analyticOn : AnalyticOnNhd ℂ f U
  mapsTo : MapsTo f U V
  /-- every fibre over `V` is a pair of points (possibly a doubled point) -/
  fiber_pair : ∀ w ∈ V, ∃ z₁ z₂, U ∩ f ⁻¹' {w} = {z₁, z₂}
  /-- the degree is exactly two -/
  degree_two : ∃ w ∈ V, ∃ z₁ ∈ U, ∃ z₂ ∈ U, z₁ ≠ z₂ ∧ f z₁ = w ∧ f z₂ = w

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit
stays in `U`. -/

theorem quadLike_K_eq (hR : 1 + ‖c‖ < R) :
    (quadLike c R hR).K = {z : ℂ | ∀ n : ℕ, ‖(quadMap c)^[n] z‖ ≤ R} := by
  have hδ := quadMap_escape_pos hR
  ext z
  simp only [QuadraticLike.K, quadLike, mem_setOf_eq]
  constructor
  · intro h n
    match n with
    | 0 =>
        by_contra hc
        push_neg at hc
        have h1 := norm_quadMap_ge hR hc.le
        have h2 : ‖quadMap c z‖ < R := mem_quadU_iff.1 (h 0)
        simp only [Function.iterate_zero_apply] at *
        linarith
    | (n + 1) =>
        have h2 : ‖quadMap c ((quadMap c)^[n] z)‖ < R := mem_quadU_iff.1 (h n)
        rw [Function.iterate_succ_apply']
        exact h2.le
  · intro h n
    rw [mem_quadU_iff]
    by_contra hc
    push_neg at hc
    have h1 : R ≤ ‖quadMap c ((quadMap c)^[n] z)‖ := hc
    have h2 : quadMap c ((quadMap c)^[n] z) = (quadMap c)^[n + 1] z :=
      (Function.iterate_succ_apply' _ _ _).symm
    rw [h2] at h1
    have h3 := norm_iterate_escape hR h1 1
    have h4 : ((quadMap c)^[1]) ((quadMap c)^[n + 1] z) = (quadMap c)^[n + 2] z := by
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [h4] at h3
    have h5 := h (n + 2)
    push_cast at h3
    linarith

/-- The filled Julia set of the quadratic-like restriction is exactly the classical filled
Julia set of the polynomial `z ↦ z ^ 2 + c`: the set of points with bounded forward orbit. -/
