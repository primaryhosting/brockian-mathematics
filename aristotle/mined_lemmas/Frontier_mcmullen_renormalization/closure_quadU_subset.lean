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

theorem closure_quadU_subset (hR : 1 + ‖c‖ < R) : closure (quadU c R) ⊆ ball 0 R := by
  have hRpos : 0 < R := R_pos hR
  set r := Real.sqrt (R + ‖c‖) with hr
  have hsub : quadU c R ⊆ closedBall 0 r := by
    intro z hz
    have hzn : ‖quadMap c z‖ < R := mem_quadU_iff.1 hz
    have h1 : ‖z‖ ^ 2 ≤ R + ‖c‖ := by
      have h2 : ‖z ^ 2‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := by
        have h3 : ‖z ^ 2‖ = ‖(z ^ 2 + c) - c‖ := by ring_nf
        rw [h3]
        exact norm_sub_le _ _
      rw [norm_pow] at *
      simp only [quadMap] at hzn
      linarith
    simp only [mem_closedBall, dist_zero_right, hr]
    exact Real.le_sqrt_of_sq_le h1
  have hrR : r < R := by
    rw [hr]
    have h : R + ‖c‖ < R ^ 2 := by nlinarith [norm_nonneg c]
    calc Real.sqrt (R + ‖c‖) < Real.sqrt (R ^ 2) := Real.sqrt_lt_sqrt (by positivity) h
      _ = R := by rw [Real.sqrt_sq hRpos.le]
  calc closure (quadU c R) ⊆ closure (closedBall 0 r) := closure_mono hsub
    _ = closedBall 0 r := isClosed_closedBall.closure_eq
    _ ⊆ ball 0 R := by
        intro x hx
        simp only [mem_closedBall, dist_zero_right] at hx
        simp only [mem_ball, dist_zero_right]
        linarith

