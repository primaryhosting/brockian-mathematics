/-
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, distinct, and the
sum of the divisors of each equals `m + n + 1` (equivalently, the sum of the *proper* divisors of
each one is the other one plus one). -/

lemma two_mul_sigma_one_le (k : ℕ) : 2 * σ 1 k ≤ k * (k + 1) := by
  rw [sigma_one_apply]
  have hsub : k.divisors ⊆ Finset.range (k + 1) := fun d hd => by
    simp only [Finset.mem_range]; exact Nat.lt_succ_of_le (Nat.divisor_le hd)
  have h1 := Finset.sum_le_sum_of_subset (f := _root_.id) hsub
  have h2 : (∑ i ∈ Finset.range (k + 1), i) * 2 = (k + 1) * k := by
    simpa using Finset.sum_range_id_mul_two (k + 1)
  have h3 : k * (k + 1) = (k + 1) * k := Nat.mul_comm _ _
  simp only [_root_.id] at h1
  omega

/-- If `q = 3 * r` with `r ≥ 2` and `r ≠ 3`, then `1, 3, r, 3 * r` are four distinct divisors
of `q`, hence `σ 1 q ≥ 4 + r + 3 * r`. -/
