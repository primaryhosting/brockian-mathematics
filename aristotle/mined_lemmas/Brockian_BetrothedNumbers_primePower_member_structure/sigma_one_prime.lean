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

lemma sigma_one_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simpa [Finset.sum_range_succ, Nat.add_comm] using this

/-- Crude upper bound `2 * σ 1 k ≤ k * (k + 1)`, since every divisor of `k` lies in `[1, k]`. -/
