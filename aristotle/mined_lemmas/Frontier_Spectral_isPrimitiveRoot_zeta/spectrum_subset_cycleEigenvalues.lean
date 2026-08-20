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

theorem spectrum_subset_cycleEigenvalues (n : ℕ) (hn : n ≠ 0) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ (cycleLaplacian n)) : ∃ k : Fin n, μ = cycleEigenvalue n k := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨u, hu, hu0⟩ := hμ.exists_hasEigenvector
  have h1 := (cycleLaplacian_eq_smul_iff n hn u μ).mp (Module.End.mem_eigenspace_iff.mp hu)
  have hrep : (fourierBasis n hn).repr u ≠ 0 := by
    intro h
    exact hu0 ((fourierBasis n hn).repr.injective (by simpa using h))
  obtain ⟨k, hk⟩ : ∃ k, (fourierBasis n hn).repr u k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hrep (by ext k; simpa using hcon k)
  rcases mul_eq_zero.mp (h1 k) with h | h
  · exact ⟨k, (sub_eq_zero.mp h).symm⟩
  · exact absurd h hk

/-- The eigenspace of `μ` is spanned by the Fourier vectors with eigenvalue `μ`. -/
