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

lemma trace_pow_mul_conjTranspose (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v)
    (hM : ∀ j k, M j k = ∑ i, (s i : ℂ) * u i j * v i k) (k : ℕ) :
    Matrix.trace ((M * Mᴴ) ^ (k + 1)) = ∑ i, (((s i : ℂ) ^ 2)) ^ (k + 1) := by
  rw [mul_conjTranspose_of_decomp hv hM, pow_sum_outer hu, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.trace_smul, trace_outer, (orthonormal_iff_ite.mp hu) i i]
  simp

end

/-! ### Uniqueness of the Schmidt coefficients -/

