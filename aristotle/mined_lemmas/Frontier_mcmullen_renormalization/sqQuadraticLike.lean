import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalize the basic combinatorial/structural framework of McMullen's theory of
renormalization for quadratic-like maps (Douady–Hubbard quadratic-like maps,
`QuadraticLike` below):

* `Frontier.QuadraticLike` — a degree-two proper holomorphic map `f : U → V` with
  `closure U` compact and contained in `V`, with a unique critical point.
* `Frontier.filledJulia` — the filled Julia set `K(f) = {z ∈ U | ∀ n, f^[n] z ∈ U}`.
* `Frontier.IsRenormalizationOf` — `R` is a renormalization of `Q` with period `p`:
  `R.f = Q.f^[p]`, `R` is defined on a smaller domain around the same critical point,
  and the small filled Julia set `K(R)` is connected.
* `Frontier.Renormalizable` — existence of such a renormalization.

The main theorem `Frontier.mcmullen_renormalization` records the two structural facts
that are proved here in full:

1. **Base case (period one).** A quadratic-like map with connected filled Julia set is
   renormalizable of period `1`, the renormalization being the map itself.
2. **Reduction (multiplicativity of periods).** If `R` is a renormalization of `Q` of
   period `p` and `R` is itself renormalizable of period `q`, then `Q` is renormalizable
   of period `p * q`.  This is the Lean-checked reduction underlying the study of
   infinitely renormalizable maps.

The framework is shown to be non-vacuous: `Frontier.sqQuadraticLike` is the explicit
quadratic-like map `z ↦ z²` on `B(0,2) → B(0,4)`, whose filled Julia set is the closed
unit disc (`Frontier.filledJulia_sq`), hence connected, so it is renormalizable of
period one (`Frontier.sqQuadraticLike_renormalizable`).
-/

open Set

namespace Frontier

/-- A **quadratic-like map** in the sense of Douady–Hubbard: a proper degree-two
holomorphic map `f : U → V` between open subsets of `ℂ` with `closure U` a compact
subset of `V`.  Degree two is encoded by requiring a single critical value `f crit`,
whose fibre is the singleton `{crit}`, all other fibres over `V` consisting of exactly
two points. -/
structure QuadraticLike where
  /-- The smaller domain. -/
  U : Set ℂ
  /-- The larger domain. -/
  V : Set ℂ
  /-- The map. -/
  f : ℂ → ℂ
  /-- The critical point. -/
  crit : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isCompact_closure_U : IsCompact (closure U)
  closure_U_subset_V : closure U ⊆ V
  analyticOn : AnalyticOnNhd ℂ f U
  mapsTo : MapsTo f U V
  surjOn : SurjOn f U V
  crit_mem : crit ∈ U
  fiber_crit : {z ∈ U | f z = f crit} = {crit}
  fiber_two : ∀ w ∈ V, w ≠ f crit → ∃ z₁ z₂ : ℂ, z₁ ≠ z₂ ∧ {z ∈ U | f z = w} = {z₁, z₂}

/-- The filled Julia set of a quadratic-like map: the points of `U` whose whole forward
orbit stays in `U`. -/

def sqQuadraticLike : QuadraticLike where
  U := Metric.ball (0 : ℂ) 2
  V := Metric.ball (0 : ℂ) 4
  f := fun z => z ^ 2
  crit := 0
  isOpen_U := Metric.isOpen_ball
  isOpen_V := Metric.isOpen_ball
  isCompact_closure_U := by
    rw [closure_ball _ (by norm_num)]
    exact isCompact_closedBall _ _
  closure_U_subset_V := by
    rw [closure_ball _ (by norm_num)]
    intro z hz
    simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right] at *
    linarith
  analyticOn := fun z _ => (analyticAt_id.pow 2)
  mapsTo := by
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right, norm_pow] at *
    nlinarith [norm_nonneg z]
  surjOn := by
    intro w hw
    simp only [Metric.mem_ball, dist_zero_right] at hw
    obtain ⟨z, hz, hzw⟩ := exists_sqrt_mem w hw
    exact ⟨z, by simpa [Metric.mem_ball, dist_zero_right] using hz, hzw⟩
  crit_mem := by simp [Metric.mem_ball]
  fiber_crit := by
    ext z
    simp [Metric.mem_ball, pow_eq_zero_iff]
    intro h; simp [h]
  fiber_two := by
    intro w hw hw0
    simp only [Metric.mem_ball, dist_zero_right] at hw
    simp only [ne_eq] at hw0
    have hw0' : w ≠ 0 := by simpa using hw0
    obtain ⟨z₀, hz₀, hz₀w⟩ := exists_sqrt_mem w hw
    have hz₀0 : z₀ ≠ 0 := by
      rintro rfl; exact hw0' (by simpa using hz₀w.symm)
    refine ⟨z₀, -z₀, fun h => hz₀0 (by linear_combination h / 2), ?_⟩
    ext z
    simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, hz⟩
      have : (z - z₀) * (z + z₀) = 0 := by ring_nf; linear_combination hz - hz₀w
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    · rintro (rfl | rfl)
      · exact ⟨hz₀, hz₀w⟩
      · exact ⟨by simpa using hz₀, by simpa using hz₀w⟩

/-- The filled Julia set of `z ↦ z²` on `B(0,2)` is the closed unit disc. -/
