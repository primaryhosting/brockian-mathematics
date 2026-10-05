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

theorem quadLike_K_eq_bounded_orbit (hR : 1 + ‖c‖ < R) :
    (quadLike c R hR).K
      = {z : ℂ | Bornology.IsBounded (Set.range fun n : ℕ => (quadMap c)^[n] z)} := by
  have hδ := quadMap_escape_pos hR
  rw [quadLike_K_eq hR]
  ext z
  simp only [mem_setOf_eq]
  constructor
  · intro h
    rw [isBounded_iff_forall_norm_le]
    exact ⟨R, by rintro x ⟨n, rfl⟩; exact h n⟩
  · intro h n
    rw [isBounded_iff_forall_norm_le] at h
    obtain ⟨M, hM⟩ := h
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := exists_nat_gt ((M - ‖(quadMap c)^[n] z‖) / (R * (R - 1) - ‖c‖))
    have h1 := norm_iterate_escape hR hcon.le k
    have h2 : ((quadMap c)^[k]) ((quadMap c)^[n] z) = (quadMap c)^[n + k] z := by
      rw [← Function.iterate_add_apply]
      ring_nf
    rw [h2] at h1
    have h3 : ‖(quadMap c)^[n + k] z‖ ≤ M := hM _ ⟨n + k, rfl⟩
    have h4 : (M - ‖(quadMap c)^[n] z‖) < k * (R * (R - 1) - ‖c‖) := by
      rw [div_lt_iff₀ hδ] at hk
      exact hk
    linarith

/-- The filled Julia set is non-empty: it contains a fixed point of `z ↦ z ^ 2 + c`. -/
