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

lemma geom_sum_two (b : ℕ) : (∑ i ∈ Finset.range b, 2 ^ i) + 1 = 2 ^ b := by
  induction b with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ]; omega

/-! ### The partner of a prime power -/

/-- If `p ^ a` belongs to a betrothed pair with partner `n`, then
`n + 1 = 1 + p + ⋯ + p ^ (a - 1)`. -/
