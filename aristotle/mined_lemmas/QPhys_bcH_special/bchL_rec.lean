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

lemma bchL_rec (hc : c = a * b - b * a) (hac : Commute a c) (N : ℕ) :
    ((N + 2 : ℕ) : ℚ) • bchL a b (N + 2)
      = (a + b) * bchL a b (N + 1) + c * bchL a b N := by
  have hA : a * bchL a b (N + 1)
      = ∑ m ∈ range (N + 3), ((m : ℚ) * ((m ! : ℚ) * ((N + 2 - m)! : ℚ))⁻¹) •
          (a ^ m * b ^ (N + 2 - m)) := by
    rw [Finset.sum_range_succ' _ (N + 2), bchL, Finset.mul_sum]
    simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero, Nat.succ_sub_succ]
    refine (Finset.sum_congr rfl fun m hm => ?_).symm
    rw [mul_smul_comm, ← mul_assoc, ← pow_succ']
    congr 1
    push_cast [Nat.factorial_succ]
    have h1 : (m ! : ℚ) ≠ 0 := by positivity
    have h2 : ((N + 1 - m)! : ℚ) ≠ 0 := by positivity
    field_simp
  have hB1 : b * bchL a b (N + 1)
      = (∑ m ∈ range (N + 2), ((m ! : ℚ) * ((N + 1 - m)! : ℚ))⁻¹ • (a ^ m * b ^ (N + 2 - m)))
        - ∑ m ∈ range (N + 2), ((m : ℚ) * ((m ! : ℚ) * ((N + 1 - m)! : ℚ))⁻¹) •
            (c * (a ^ (m - 1) * b ^ (N + 1 - m))) := by
    rw [bchL, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ N + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hex : N + 2 - m = (N + 1 - m) + 1 := by omega
    rw [hex, mul_smul_comm, ← mul_assoc, mul_pow_comm_of_central hc hac, sub_mul, smul_sub,
      mul_assoc (a ^ m) b, ← pow_succ', smul_mul_assoc, mul_assoc, smul_smul, mul_comm ((m : ℚ))]
  have hB2 : ∑ m ∈ range (N + 2), ((m ! : ℚ) * ((N + 1 - m)! : ℚ))⁻¹ • (a ^ m * b ^ (N + 2 - m))
      = ∑ m ∈ range (N + 3), (((N + 2 - m : ℕ) : ℚ) * ((m ! : ℚ) * ((N + 2 - m)! : ℚ))⁻¹) •
          (a ^ m * b ^ (N + 2 - m)) := by
    conv_rhs => rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ N + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hex : N + 2 - m = (N + 1 - m) + 1 := by omega
    rw [hex]
    congr 1
    push_cast [Nat.factorial_succ]
    have h1 : (m ! : ℚ) ≠ 0 := by positivity
    have h2 : ((N + 1 - m)! : ℚ) ≠ 0 := by positivity
    field_simp
  have hB3 : ∑ m ∈ range (N + 2), ((m : ℚ) * ((m ! : ℚ) * ((N + 1 - m)! : ℚ))⁻¹) •
        (c * (a ^ (m - 1) * b ^ (N + 1 - m))) = c * bchL a b N := by
    rw [bchL, Finset.mul_sum, Finset.sum_range_succ' _ (N + 1)]
    simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hex : N + 1 - (m + 1) = N - m := by omega
    rw [hex, mul_smul_comm]
    simp only [Nat.add_sub_cancel]
    congr 1
    push_cast [Nat.factorial_succ]
    have h1 : (m ! : ℚ) ≠ 0 := by positivity
    have h2 : ((N - m)! : ℚ) ≠ 0 := by positivity
    field_simp
  have hC : ((N + 2 : ℕ) : ℚ) • bchL a b (N + 2)
      = ∑ m ∈ range (N + 3), (((N + 2 : ℕ) : ℚ) * ((m ! : ℚ) * ((N + 2 - m)! : ℚ))⁻¹) •
          (a ^ m * b ^ (N + 2 - m)) := by
    rw [bchL, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
  rw [hC, add_mul, hA, hB1, hB2, hB3, add_assoc, sub_add_cancel, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ N + 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rw [← add_smul]
  congr 1
  have hcast : ((N + 2 - m : ℕ) : ℚ) = ((N + 2 : ℕ) : ℚ) - (m : ℚ) := by
    push_cast [Nat.cast_sub hm']
    ring
  rw [hcast]
  ring

