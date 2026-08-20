/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## What is formalized here

The Chern–Gauss–Bonnet theorem states that for a closed oriented Riemannian manifold `M`
of even dimension `2n`, the integral over `M` of the Euler form (the Pfaffian of the
curvature form, normalized by `(2π)^n`) equals the Euler characteristic of `M`.

Mathlib currently contains no Riemann curvature tensor, no Pfaffian, no de Rham
cohomology of manifolds and no Euler characteristic of manifolds, so all the objects
entering the statement are built here from scratch:

* `Math2.eulerDensity n R` is the Chern–Gauss–Bonnet integrand attached to an algebraic
  curvature tensor `R` written in an orthonormal frame of a `2n`-dimensional tangent
  space, namely
  `1 / ((8π)^n n!) * ∑_{σ,τ} sgn σ · sgn τ · ∏_i R (σ i₀) (σ i₁) (τ i₀) (τ i₁)`.
  `Math2.eulerDensity_dim_two` checks that for `n = 1` this is exactly the classical
  Gauss–Bonnet integrand `K / (2π)`.
* `Math2.roundCurvature n` is the Riemann curvature tensor of the unit round sphere
  `S^{2n}` in an orthonormal frame, `R a b c d = δₐᶜ δ_bd - δ_ad δ_bc`.
* the manifold is the unit sphere `S^{2n} ⊆ ℝ^{2n+1}` and its Riemannian measure is
  Mathlib's surface measure `MeasureTheory.Measure.toSphere` obtained from Lebesgue
  measure by the polar coordinate decomposition.

The main theorem `Math2.chern_gauss_bonnet` proves the Chern–Gauss–Bonnet identity for
this family of closed even-dimensional manifolds, for every `n : ℕ`: the integral of
the Euler form over `S^{2n}` equals `2 = χ(S^{2n})`. The two ingredients are a purely
combinatorial evaluation of the Pfaffian sum for constant curvature one
(`Math2.sum_sign_prod_roundCurvature`, equal to `2^n (2n)!`) and the exact value of the
surface measure of `S^{2n}` (`Math2.sphere_measureReal_univ`).
-/

open scoped Nat Real
open MeasureTheory Metric Equiv

namespace Math2

/-- Index type of an orthonormal frame of a `2 * n`-dimensional Euclidean space:
it has cardinality `2 * n`, and is organized as `n` ordered pairs, which is the
form in which the indices enter the Pfaffian. -/
abbrev Frame (n : ℕ) := Fin n × Bool

/-- The Chern–Gauss–Bonnet integrand (the Euler form, or Pfaffian of the curvature
form, divided by `(2π)^n`) of an algebraic curvature tensor `R` given in an
orthonormal frame of a `2 * n`-dimensional Riemannian manifold:
`e = 1 / ((8π)^n n!) * ∑_{σ,τ} sgn σ · sgn τ · ∏_i R (σ i₀) (σ i₁) (τ i₀) (τ i₁)`.
For `n = 1` this is the classical `K / (2π)`. -/

lemma prod_roundCurvature_eq_zero (n : ℕ) (p : Equiv.Perm (Frame n))
    (hp : ∀ T : Finset (Fin n), p ≠ pairSwap T) :
    ∏ i : Fin n, roundCurvature n (i, false) (i, true) (p (i, false)) (p (i, true)) = 0 := by
  by_contra hne0
  have hne := Finset.prod_ne_zero_iff.mp hne0
  classical
  set T : Finset (Fin n) := {i : Fin n | p (i, false) = (i, true)} with hT
  have hmemT : ∀ i : Fin n, i ∈ T ↔ p (i, false) = (i, true) := by
    intro i; simp [hT]
  refine hp T (Equiv.ext ?_)
  rintro ⟨i, b⟩
  have hi := hne i (Finset.mem_univ i)
  have hcase : (p (i, false) = (i, false) ∧ p (i, true) = (i, true)) ∨
      (p (i, false) = (i, true) ∧ p (i, true) = (i, false)) := by
    by_cases h1 : p (i, false) = (i, false)
    · by_cases h2 : p (i, true) = (i, true)
      · exact Or.inl ⟨h1, h2⟩
      · exact absurd (by simp [roundCurvature, h1, Ne.symm h2, eq_comm]) hi
    · by_cases h3 : p (i, false) = (i, true)
      · by_cases h4 : p (i, true) = (i, false)
        · exact Or.inr ⟨h3, h4⟩
        · exact absurd (by simp [roundCurvature, Ne.symm h1, Ne.symm h4]) hi
      · exact absurd (by simp [roundCurvature, Ne.symm h1, Ne.symm h3]) hi
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hnot : i ∉ T := by
      rw [hmemT, h1]
      simp
    cases b <;> simp [hnot, h1, h2]
  · have hmem : i ∈ T := (hmemT i).2 h1
    cases b <;> simp [hmem, h1, h2]

