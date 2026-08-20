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

lemma sigma_one_three_mul_ge {r : ℕ} (hr : 2 ≤ r) (hr3 : r ≠ 3) :
    1 + 3 + r + 3 * r ≤ σ 1 (3 * r) := by
  rw [sigma_one_apply]
  have hq : 3 * r ≠ 0 := by omega
  have hsub : ({1, 3, r, 3 * r} : Finset ℕ) ⊆ (3 * r).divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [Nat.mem_divisors, hq]
  have h1 := Finset.sum_le_sum_of_subset (f := _root_.id) hsub
  simp only [_root_.id] at h1
  have hsum : ∑ d ∈ ({1, 3, r, 3 * r} : Finset ℕ), d = 1 + 3 + r + 3 * r := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
      Finset.sum_insert (by simp; omega), Finset.sum_singleton]
    ring
  omega

/-! ### Geometric sums -/

/-- For odd `p`, the geometric sum `1 + p + ⋯ + p ^ (k - 1)` has the same parity as `k`. -/
