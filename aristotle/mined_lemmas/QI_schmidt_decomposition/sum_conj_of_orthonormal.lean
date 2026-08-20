import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Statement: Every bipartite pure state has a Schmidt decomposition with unique Schmidt coefficients.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Matrix

namespace QI

/-! ### Power sums determine a finite multiset of positive reals -/

open Polynomial in
/-- If two multisets of positive reals have the same power sums `∑ xᵏ` for every `k ≥ 1`,
they are equal. -/

lemma sum_conj_of_orthonormal {N r : ℕ} {v : Fin r → EuclideanSpace ℂ (Fin N)}
    (hv : Orthonormal ℂ v) (i l : Fin r) :
    ∑ k, v i k * (starRingEnd ℂ) (v l k) = if i = l then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp hv) l i
  rw [PiLp.inner_apply] at h
  simp only [RCLike.inner_apply] at h
  simpa [mul_comm, eq_comm] using h

/-! ### The Schmidt decomposition predicate -/

/-- `IsSchmidtDecomposition psi s u v` says that the bipartite state `psi` (a vector in
`ℂ^m ⊗ ℂ^n`, presented via its amplitudes indexed by pairs) is written as
`∑ i, s i • (u i ⊗ v i)` with strictly positive coefficients `s i` and orthonormal
families `u`, `v` in the two factors. -/
structure IsSchmidtDecomposition {m n r : ℕ} (psi : EuclideanSpace ℂ (Fin m × Fin n))
    (s : Fin r → ℝ) (u : Fin r → EuclideanSpace ℂ (Fin m))
    (v : Fin r → EuclideanSpace ℂ (Fin n)) : Prop where
  pos : ∀ i, 0 < s i
  left_orthonormal : Orthonormal ℂ u
  right_orthonormal : Orthonormal ℂ v
  amp : ∀ j k, psi (j, k) = ∑ i, (s i : ℂ) * u i j * v i k

/-! ### The Gram matrix of a decomposition -/

section

variable {m n r : ℕ} {M : Matrix (Fin m) (Fin n) ℂ} {s : Fin r → ℝ}
  {u : Fin r → EuclideanSpace ℂ (Fin m)} {v : Fin r → EuclideanSpace ℂ (Fin n)}

