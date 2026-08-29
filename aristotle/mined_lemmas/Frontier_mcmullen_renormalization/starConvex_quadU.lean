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

theorem starConvex_quadU (hR : 1 + ‖c‖ < R) : StarConvex ℝ 0 (quadU c R) := by
  intro z hz a b _ hb hab
  have hzn : ‖quadMap c z‖ < R := mem_quadU_iff.1 hz
  have hc : ‖c‖ < R := norm_c_lt hR
  rw [smul_zero, zero_add, mem_quadU_iff]
  have key : quadMap c (b • z) = (b : ℂ) ^ 2 * (z ^ 2 + c) + (1 - (b : ℂ) ^ 2) * c := by
    simp only [quadMap, Complex.real_smul]; ring
  have hb1 : b ≤ 1 := by nlinarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hX : ‖z ^ 2 + c‖ < R := hzn
  rw [key]
  calc ‖(b : ℂ) ^ 2 * (z ^ 2 + c) + (1 - (b : ℂ) ^ 2) * c‖
      ≤ ‖(b : ℂ) ^ 2 * (z ^ 2 + c)‖ + ‖(1 - (b : ℂ) ^ 2) * c‖ := norm_add_le _ _
    _ = b ^ 2 * ‖z ^ 2 + c‖ + (1 - b ^ 2) * ‖c‖ := by
        rw [norm_mul, norm_mul]
        congr 1
        · congr 1
          simp [abs_of_nonneg hb]
        · congr 1
          have h3 : (1 : ℂ) - (b : ℂ) ^ 2 = ((1 - b ^ 2 : ℝ) : ℂ) := by push_cast; ring
          rw [h3, Complex.norm_real]
          exact abs_of_nonneg (by nlinarith)
    _ < R := by
        rcases eq_or_lt_of_le hb with h | h
        · simp [← h]; linarith
        · have hbb : 0 < b ^ 2 := by positivity
          nlinarith [norm_nonneg (z ^ 2 + c), norm_nonneg c]

