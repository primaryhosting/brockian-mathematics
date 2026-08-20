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

lemma pow_sum_outer (hu : Orthonormal ℂ u) (c : Fin r → ℂ) (k : ℕ) :
    (∑ i, c i • outer (u i) (u i)) ^ (k + 1) = ∑ i, (c i) ^ (k + 1) • outer (u i) (u i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [smul_mul_smul_comm, outer_mul_outer, (orthonormal_iff_ite.mp hu) i i]
      simp [pow_succ]
    · intro l _ hl
      rw [smul_mul_smul_comm, outer_mul_outer, (orthonormal_iff_ite.mp hu) i l,
        if_neg (Ne.symm hl)]
      simp
    · simp

