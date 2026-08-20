import Mathlib
/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the very first command in a file, so the header
comment appears immediately after it.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace QPhys

open Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- The degree-`N` homogeneous component of the product `exp a * exp b`. -/

lemma bchR_rec (hcd : Commute c d) (N : ℕ) :
    ((N + 2 : ℕ) : ℚ) • bchR c d (N + 2) = d * bchR c d (N + 1) + c * bchR c d N := by
  have hD : d * bchR c d (N + 1)
      = ∑ j ∈ range (N + 3), bchCoef (N + 1) j • (c ^ j * d ^ (N + 2 - 2 * j)) := by
    rw [bchR, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show bchCoef (N + 1) (N + 2) = 0 from by rw [bchCoef, if_neg (by omega)]]
    simp only [zero_smul, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj2 : 2 * j ≤ N + 1
    · have hex : N + 2 - 2 * j = (N + 1 - 2 * j) + 1 := by omega
      rw [hex, mul_smul_comm, ← mul_assoc, (hcd.symm.pow_right j).eq, mul_assoc, ← pow_succ']
    · rw [bchCoef, if_neg hj2]
      simp
  have hE : c * bchR c d N
      = ∑ j ∈ range (N + 3), (if j = 0 then 0 else bchCoef N (j - 1)) •
          (c ^ j * d ^ (N + 2 - 2 * j)) := by
    rw [bchR, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_range_succ' _ (N + 2), Finset.sum_range_succ]
    rw [show bchCoef N (N + 1 + 1 - 1) = 0 from by rw [bchCoef, if_neg (by omega)]]
    simp only [Nat.succ_ne_zero, if_false, zero_smul, add_zero, Nat.add_sub_cancel, reduceIte]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hex : N + 2 - 2 * (j + 1) = N - 2 * j := by omega
    rw [hex, mul_smul_comm, ← mul_assoc, ← pow_succ']
  have hF : ((N + 2 : ℕ) : ℚ) • bchR c d (N + 2)
      = ∑ j ∈ range (N + 3), (((N + 2 : ℕ) : ℚ) * bchCoef (N + 2) j) •
          (c ^ j * d ^ (N + 2 - 2 * j)) := by
    rw [bchR, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  rw [hF, hD, hE, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [← add_smul, bchCoef_rec]

/-- Cancelling a nonzero rational scalar. -/
