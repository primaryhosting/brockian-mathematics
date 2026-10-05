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

theorem quadLike_K_nonempty (hR : 1 + ‖c‖ < R) : (quadLike c R hR).K.Nonempty := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (1 - 4 * c) (n := 2) (by norm_num)
  set z₀ : ℂ := (1 + s) / 2 with hz₀
  have hfix : quadMap c z₀ = z₀ := by
    simp only [quadMap, hz₀]
    field_simp
    linear_combination hs
  have hiter : ∀ n : ℕ, (quadMap c)^[n] z₀ = z₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, hfix]
  have hnorm : ‖z₀‖ ≤ R := by
    by_contra hcon
    push_neg at hcon
    have h1 := norm_quadMap_ge hR hcon.le
    rw [hfix] at h1
    have := quadMap_escape_pos hR
    linarith
  refine ⟨z₀, ?_⟩
  rw [quadLike_K_eq hR]
  intro n
  rw [hiter n]
  exact hnorm

/-- The filled Julia set of the quadratic-like restriction is compact. -/
