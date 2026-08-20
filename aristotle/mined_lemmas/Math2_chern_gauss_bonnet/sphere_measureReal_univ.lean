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

lemma sphere_measureReal_univ (n : ℕ) :
    (volume.toSphere (E := EuclideanSpace ℝ (Fin (2 * n + 1)))).real Set.univ =
      2 ^ (n + 1) * π ^ n / ((2 * n - 1)‼ : ℝ) := by
  rw [Measure.toSphere_real_apply_univ, measureReal_def, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  have hG : Real.Gamma ((2 * n + 1 : ℕ) / 2 + 1) = ((2 * n + 1)‼ : ℝ) * √π / 2 ^ (n + 1) := by
    have h : ((2 * n + 1 : ℕ) : ℝ) / 2 + 1 = ((n + 1 : ℕ) : ℝ) + 1 / 2 := by push_cast; ring
    rw [h, Real.Gamma_nat_add_half]
    congr 2
  have hsq : √π ^ (2 * n + 1) = π ^ n * √π := by
    rw [pow_succ, pow_mul, Real.sq_sqrt Real.pi_nonneg]
  have hd : ((2 * n + 1)‼ : ℝ) = (2 * n + 1) * ((2 * n - 1)‼ : ℝ) := by
    rw [show (2 * n + 1)‼ = (2 * n + 1) * (2 * n - 1)‼ from Nat.doubleFactorial_add_one (2 * n)]
    push_cast; ring
  have hpos : (0 : ℝ) < ((2 * n - 1)‼ : ℝ) := by exact_mod_cast Nat.doubleFactorial_pos _
  have hspi : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  rw [hG, hsq, ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin, hd]
  push_cast
  field_simp

