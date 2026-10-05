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

theorem fiber_quadMap : ∀ w ∈ ball (0 : ℂ) R,
    ∃ z₁ z₂, quadU c R ∩ quadMap c ⁻¹' {w} = {z₁, z₂} := by
  intro w hw
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w - c) (n := 2) (by norm_num)
  refine ⟨s, -s, ?_⟩
  have hmem : ∀ t : ℂ, t ^ 2 = w - c → t ∈ quadU c R ∩ quadMap c ⁻¹' {w} := by
    intro t ht
    have hfz : quadMap c t = w := by simp only [quadMap, ht]; ring
    refine ⟨?_, by simp [hfz]⟩
    rw [mem_quadU_iff, hfz]
    simpa [mem_ball, dist_eq_norm] using hw
  apply Subset.antisymm
  · rintro z ⟨-, hz2⟩
    simp only [mem_preimage, mem_singleton_iff, quadMap] at hz2
    have hfac : (z - s) * (z + s) = 0 := by
      have h : z ^ 2 = s ^ 2 := by rw [hs]; linear_combination hz2
      linear_combination h
    rcases mul_eq_zero.1 hfac with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (by simpa using eq_neg_of_add_eq_zero_left h)
  · rintro z (rfl | rfl)
    · exact hmem _ hs
    · exact hmem _ (by rw [neg_pow]; simpa using hs)

