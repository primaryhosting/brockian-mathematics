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

lemma sum_sign_prod_roundCurvature_aux (n : ℕ) :
    ∑ p : Equiv.Perm (Frame n), (Equiv.Perm.sign p : ℝ) *
      ∏ i : Fin n, roundCurvature n (i, false) (i, true) (p (i, false)) (p (i, true))
      = 2 ^ n := by
  classical
  set g : Equiv.Perm (Frame n) → ℝ := fun p => (Equiv.Perm.sign p : ℝ) *
    ∏ i : Fin n, roundCurvature n (i, false) (i, true) (p (i, false)) (p (i, true)) with hg
  have hinj : ∀ T ∈ (Finset.univ : Finset (Finset (Fin n))),
      ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      pairSwap T = pairSwap S → T = S := by
    intro T _ S _ h
    ext i
    have := congrArg (fun e : Equiv.Perm (Frame n) => e (i, false)) h
    simp only [pairSwap_apply] at this
    by_cases hT : i ∈ T <;> by_cases hS : i ∈ S <;> simp_all
  have himg : ∑ p ∈ (Finset.univ : Finset (Finset (Fin n))).image pairSwap, g p =
      ∑ T : Finset (Fin n), g (pairSwap T) := Finset.sum_image hinj
  have hsub : ∑ p : Equiv.Perm (Frame n), g p =
      ∑ p ∈ (Finset.univ : Finset (Finset (Fin n))).image pairSwap, g p := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro p _ hp
    have hp' : ∀ T : Finset (Fin n), p ≠ pairSwap T := by
      intro T hT
      exact hp (Finset.mem_image.2 ⟨T, Finset.mem_univ T, hT.symm⟩)
    simp [hg, prod_roundCurvature_eq_zero n p hp']
  have hone : ∀ T : Finset (Fin n), g (pairSwap T) = 1 := by
    intro T
    rw [hg]
    simp only
    rw [prod_roundCurvature_pairSwap, sign_pairSwap, ← mul_pow]
    norm_num
  rw [hsub, himg, Finset.sum_congr rfl (fun T _ => hone T)]
  simp [Finset.card_univ]

/-- The key combinatorial identity: the (unnormalized) Pfaffian sum of the constant
curvature one tensor in dimension `2 * n` equals `2 ^ n * (2 * n)!`. -/
