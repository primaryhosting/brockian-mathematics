import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# The Fourier spectrum of the combinatorial cycle Laplacian

For `n : ℕ` we work in the finite dimensional complex vector space `Fin n → ℂ` and
study the combinatorial Laplacian of the cycle graph `C n`,

  `(L v) j = 2 * v j - v (j + 1) - v (j - 1)`,

where the indices are taken in `Fin n`, i.e. cyclically (see `cycleLaplacian_apply`).
The intended range of `n` is `3 ≤ n`, but everything below is proved for every
`n ≠ 0`; the exported theorem `cycle_laplacian_spectrum` is stated for `3 ≤ n`.

The discrete Fourier vectors `vₖ j = exp (2 π I k j / n)` are eigenvectors of `L`
with eigenvalues `2 - 2 cos (2 π k / n)`, they are pairwise orthogonal, and they
form a basis of `Fin n → ℂ`.  Consequently the spectrum of `L` is exactly the set
of these numbers, and both the geometric and the algebraic multiplicity of each
eigenvalue are given by the number of Fourier modes producing it.

Main results:

* `Frontier.Spectral.fourierVec_ne_zero` — each Fourier vector is nonzero;
* `Frontier.Spectral.cycleLaplacian_fourierVec` — the eigenvalue equation;
* `Frontier.Spectral.fourierVec_orthogonal`, `Frontier.Spectral.fourierVec_inner_euclidean`,
  `Frontier.Spectral.fourierBasis` — orthogonality and the resulting basis;
* `Frontier.Spectral.finrank_eigenspace`, `Frontier.Spectral.charpoly_cycleLaplacian` —
  geometric and algebraic multiplicities;
* `Frontier.Spectral.cycle_laplacian_spectrum` — the exported spectral theorem.

This is the standard finite-dimensional spectral computation for the cycle graph; no new
mathematics is claimed, and in particular nothing is claimed about uniform spectral gaps
of families of graphs.

Scope and limitations (honest summary):

* `spectrum` is Mathlib's `spectrum ℂ (f : Module.End ℂ (Fin n → ℂ))`, i.e. the set of `μ`
  for which `μ • 1 - f` is not invertible.  No bespoke notion of spectrum is introduced.
* Orthogonality is stated as the explicit Hermitian sum `∑ j, conj (vₗ j) * vₖ j`, since the
  plain pi type `Fin n → ℂ` carries no inner product instance in Mathlib; the corresponding
  statement for Mathlib's inner product on `EuclideanSpace ℂ (Fin n)` is
  `fourierVec_inner_euclidean`.
* The Fourier vectors are orthogonal but not normalised: `∑ j, conj (vₖ j) * vₖ j = n`
  (`fourierVec_inner`).
* The proofs only use `n ≠ 0`; the hypothesis `3 ≤ n` in the exported theorem is kept
  because the cycle graph `C n` is a simple graph only for `n ≥ 3`.
* Multiplicities are covered in two ways: geometric multiplicity by `finrank_eigenspace`
  and algebraic multiplicity by `charpoly_cycleLaplacian`.  Distinct values of `k` may of
  course give the same eigenvalue (`k` and `n - k` do), which is exactly what those two
  statements account for.
-/

namespace Frontier.Spectral

open Complex Finset

/-! ### The root of unity -/

/-- The standard primitive `n`-th root of unity. -/

theorem fourierVec_inner (n : ℕ) (k l : Fin n) :
    ∑ j : Fin n, (starRingEnd ℂ) (fourierVec n l j) * fourierVec n k j
      = if k = l then (n : ℂ) else 0 := by
  have hn : n ≠ 0 := k.pos.ne'
  have hz : zeta n ≠ 0 := zeta_ne_zero n
  set y : ℂ := zeta n ^ (((k : ℕ) : ℤ) - ((l : ℕ) : ℤ)) with hy
  have key : ∀ j : Fin n,
      (starRingEnd ℂ) (fourierVec n l j) * fourierVec n k j = y ^ (j : ℕ) := by
    intro j
    rw [fourierVec_eq_zeta_pow, fourierVec_eq_zeta_pow, map_pow, conj_zeta]
    have e1 : ((zeta n)⁻¹) ^ ((l : ℕ) * (j : ℕ))
        = zeta n ^ (-(((l : ℕ) * (j : ℕ) : ℕ) : ℤ)) := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    have e2 : zeta n ^ ((k : ℕ) * (j : ℕ)) = zeta n ^ ((((k : ℕ) * (j : ℕ) : ℕ)) : ℤ) :=
      (zpow_natCast _ _).symm
    have e3 : y ^ (j : ℕ) = zeta n ^ ((((k : ℕ) : ℤ) - ((l : ℕ) : ℤ)) * ((j : ℕ) : ℤ)) := by
      rw [hy, ← zpow_natCast (zeta n ^ _) (j : ℕ), ← zpow_mul]
    rw [e1, e2, e3, ← zpow_add₀ hz]
    congr 1
    push_cast
    ring
  simp only [key]
  rw [Fin.sum_univ_eq_sum_range (fun i => y ^ i) n]
  by_cases h : k = l
  · subst h
    simp [hy]
  · rw [if_neg h]
    have hyne : y ≠ 1 := by
      intro h1
      have hdvd : ((n : ℕ) : ℤ) ∣ (((k : ℕ) : ℤ) - ((l : ℕ) : ℤ)) :=
        ((isPrimitiveRoot_zeta n hn).zpow_eq_one_iff_dvd _).mp h1
      have habs : |(((k : ℕ) : ℤ) - ((l : ℕ) : ℤ))| < (n : ℤ) := by
        have := k.isLt; have := l.isLt
        rw [abs_lt]; omega
      have := Int.eq_zero_of_abs_lt_dvd hdvd habs
      exact h (Fin.ext (by omega))
    have hyn : y ^ n = 1 := by
      rw [hy, ← zpow_natCast (zeta n ^ _) n, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, zeta_pow_self n hn, one_zpow]
    rw [geom_sum_eq hyne, hyn, sub_self, zero_div]

/-- (3a) Distinct Fourier vectors are orthogonal. -/
