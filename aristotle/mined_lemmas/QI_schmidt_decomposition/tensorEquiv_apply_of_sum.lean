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

lemma tensorEquiv_apply_of_sum {m n r : ℕ} (s : Fin r → ℝ)
    (u : Fin r → EuclideanSpace ℂ (Fin m)) (v : Fin r → EuclideanSpace ℂ (Fin n))
    (j : Fin m) (k : Fin n) :
    tensorEquiv m n (∑ i, (s i : ℂ) • (u i ⊗ₜ[ℂ] v i)) (j, k)
      = ∑ i, (s i : ℂ) * u i j * v i k := by
  rw [map_sum]
  simp only [map_smul]
  rw [show ((∑ i, (s i : ℂ) • tensorEquiv m n (u i ⊗ₜ[ℂ] v i)) :
      EuclideanSpace ℂ (Fin m × Fin n)) (j, k)
      = ∑ i, (s i : ℂ) * (tensorEquiv m n (u i ⊗ₜ[ℂ] v i)) (j, k) from by simp]
  exact Finset.sum_congr rfl fun i _ => by rw [tensorEquiv_tmul]; ring

open TensorProduct in
/-- **Schmidt decomposition, tensor product form.** Every vector of `ℂ^m ⊗ ℂ^n` is of the form
`∑ i, s i • (u i ⊗ v i)` with `s i > 0` and `u`, `v` orthonormal families, and the multiset of
the coefficients `s` is uniquely determined. -/
