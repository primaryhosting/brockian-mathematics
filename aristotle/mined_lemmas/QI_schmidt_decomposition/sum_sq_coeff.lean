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

lemma sum_sq_coeff {m n : ℕ} {psi : EuclideanSpace ℂ (Fin m × Fin n)} {r : ℕ} {s : Fin r → ℝ}
    {u : Fin r → EuclideanSpace ℂ (Fin m)} {v : Fin r → EuclideanSpace ℂ (Fin n)}
    (h : IsSchmidtDecomposition psi s u v) : ∑ i, (s i) ^ 2 = ‖psi‖ ^ 2 := by
  classical
  set M : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun j k => psi (j, k) with hMdef
  have hM : ∀ j k, M j k = ∑ i, (s i : ℂ) * u i j * v i k := fun j k => h.amp j k
  have h1 := trace_pow_mul_conjTranspose h.left_orthonormal h.right_orthonormal hM 0
  have h2 : Matrix.trace (M * Mᴴ) = ((∑ p : Fin m × Fin n, ‖psi p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, hMdef,
      Matrix.of_apply, Fintype.sum_prod_type]
    push_cast
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
      rw [← starRingEnd_apply, Complex.mul_conj']
  rw [pow_one, h2] at h1
  simp only [zero_add, pow_one] at h1
  have h3 : (∑ p : Fin m × Fin n, ‖psi p‖ ^ 2) = ∑ i, (s i) ^ 2 := by exact_mod_cast h1
  rw [← h3, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-! ### Main theorem -/

/-- **Schmidt decomposition.** Every bipartite pure state `psi ∈ ℂ^m ⊗ ℂ^n` can be written as
`psi = ∑ i, s i • (u i ⊗ v i)` with strictly positive reals `s i` and orthonormal families
`u`, `v`; the sum of the squares of the coefficients is `‖psi‖ ^ 2` (so it is `1` for a
normalized state), and the multiset of Schmidt coefficients is uniquely determined by `psi`. -/
