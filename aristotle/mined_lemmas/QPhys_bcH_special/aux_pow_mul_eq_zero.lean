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

lemma aux_pow_mul_eq_zero {r M : ℕ} (hcr : c ^ r = 0) (hR : ∀ N, M ≤ N → bchR c d N = 0) :
    ∀ t, t ≤ r → ∀ N, M + 2 * t ≤ N → c ^ (r - t) * d ^ N = 0 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro htr N hN
    have hRN : bchR c d N = 0 := hR N (by omega)
    have expand : c ^ (r - t) * bchR c d N
        = ∑ j ∈ range (N + 1), bchCoef N j • (c ^ (r - t + j) * d ^ (N - 2 * j)) := by
      rw [bchR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, ← mul_assoc, ← pow_add]
    rw [hRN, mul_zero] at expand
    rw [Finset.sum_range_succ' _ N] at expand
    have hzero : ∑ j ∈ range N, bchCoef N (j + 1) •
        (c ^ (r - t + (j + 1)) * d ^ (N - 2 * (j + 1))) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rcases le_or_gt (j + 1) t with h | h
      · have h1 : t - (j + 1) < t := by omega
        have h2 : t - (j + 1) ≤ r := by omega
        have h3 : M + 2 * (t - (j + 1)) ≤ N - 2 * (j + 1) := by omega
        have h4 := ih (t - (j + 1)) h1 h2 (N - 2 * (j + 1)) h3
        have hexp : r - (t - (j + 1)) = r - t + (j + 1) := by omega
        rw [hexp] at h4
        rw [h4, smul_zero]
      · have h5 : c ^ (r - t + (j + 1)) = 0 := pow_eq_zero_of_le (by omega) hcr
        rw [h5, zero_mul, smul_zero]
    rw [hzero, zero_add] at expand
    simp only [Nat.add_zero, Nat.mul_zero, Nat.sub_zero] at expand
    refine smul_left_cancel_rat (bchCoef_zero_ne_zero N) ?_
    rw [smul_zero]
    exact expand.symm

/-- Assembling the graded components of `exp a * exp b`. -/
