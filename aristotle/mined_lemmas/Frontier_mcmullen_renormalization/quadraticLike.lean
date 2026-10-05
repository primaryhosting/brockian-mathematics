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

theorem QuadraticLike.mapsTo_K (Q : QuadraticLike) : MapsTo Q.f Q.K Q.K := by
  intro z hz n
  rw [← Function.iterate_succ_apply]
  exact hz (n + 1)

/-- `Q'` is a renormalization of `Q` of period `p`: `Q'` is a quadratic-like restriction of
the `p`-th iterate of `Q`, and the first `p` iterates of `Q` keep the domain of `Q'` inside the
domain of `Q`. -/
structure IsRenormalization (Q Q' : QuadraticLike) (p : ℕ) : Prop where
  one_le : 1 ≤ p
  iterate : Q'.f = Q.f^[p]
  subset : Q'.U ⊆ Q.U
  iterates_mem : ∀ j < p, MapsTo (Q.f^[j]) Q'.U Q.U

/-- `Q` is renormalizable of period `p`. -/
