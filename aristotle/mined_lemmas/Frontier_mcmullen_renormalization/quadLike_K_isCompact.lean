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

theorem quadLike_K_isCompact (hR : 1 + ‖c‖ < R) : IsCompact (quadLike c R hR).K := by
  rw [quadLike_K_eq hR]
  have hcl : IsClosed {z : ℂ | ∀ n : ℕ, ‖(quadMap c)^[n] z‖ ≤ R} := by
    have : {z : ℂ | ∀ n : ℕ, ‖(quadMap c)^[n] z‖ ≤ R}
        = ⋂ n : ℕ, ((quadMap c)^[n]) ⁻¹' (closedBall 0 R) := by
      ext z; simp [mem_closedBall, dist_zero_right]
    rw [this]
    refine isClosed_iInter fun n => IsClosed.preimage ?_ isClosed_closedBall
    have hcont : Continuous (quadMap c) := by unfold quadMap; fun_prop
    exact hcont.iterate n
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) R) hcl ?_
  intro z hz
  simpa [mem_closedBall, dist_zero_right] using hz 0

/-- Dichotomy: a point outside the filled Julia set has an orbit escaping to infinity at a
definite linear rate. -/
