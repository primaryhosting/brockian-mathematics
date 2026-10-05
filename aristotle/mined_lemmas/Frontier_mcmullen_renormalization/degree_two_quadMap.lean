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

theorem degree_two_quadMap (hR : 1 + ‖c‖ < R) :
    ∃ w ∈ ball (0 : ℂ) R, ∃ z₁ ∈ quadU c R, ∃ z₂ ∈ quadU c R, z₁ ≠ z₂ ∧
      quadMap c z₁ = w ∧ quadMap c z₂ = w := by
  have hRpos : 0 < R := R_pos hR
  obtain ⟨w, hwV, hwc⟩ : ∃ w ∈ ball (0 : ℂ) R, w ≠ c := by
    by_cases h : c = 0
    · refine ⟨(R / 2 : ℝ), ?_, ?_⟩
      · simp [mem_ball, dist_eq_norm, abs_of_nonneg hRpos.le]; linarith
      · simp [h]; intro hh; linarith
    · exact ⟨0, by simp [mem_ball, hRpos], fun hh => h hh.symm⟩
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w - c) (n := 2) (by norm_num)
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    exact hwc (sub_eq_zero.1 hs.symm)
  have hmem : ∀ t : ℂ, t ^ 2 = w - c → t ∈ quadU c R ∧ quadMap c t = w := by
    intro t ht
    have hfz : quadMap c t = w := by simp only [quadMap, ht]; ring
    refine ⟨?_, hfz⟩
    rw [mem_quadU_iff, hfz]
    simpa [mem_ball, dist_eq_norm] using hwV
  obtain ⟨h1, h1'⟩ := hmem s hs
  obtain ⟨h2, h2'⟩ := hmem (-s) (by rw [neg_pow]; simpa using hs)
  exact ⟨w, hwV, s, h1, -s, h2, fun h => hs0 (by linear_combination h / 2), h1', h2'⟩

/-- The quadratic polynomial `z ↦ z ^ 2 + c`, restricted to `quadU c R`, is a quadratic-like
map onto the disc of radius `R`, as soon as `1 + ‖c‖ < R`. -/
