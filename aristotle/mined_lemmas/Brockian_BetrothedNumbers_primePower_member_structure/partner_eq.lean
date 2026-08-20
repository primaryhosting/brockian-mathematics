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

lemma partner_eq {p a n : ℕ} (hp : p.Prime) (h : IsBetrothedPair (p ^ a) n) :
    n + 1 = ∑ i ∈ Finset.range a, p ^ i := by
  obtain ⟨-, -, -, h1, -⟩ := h
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ] at h1
  omega

/-! ### The main structure theorem -/

/-- **Hagis–Lord, Proposition 4.**  If a prime power `p ^ a` is a member of a betrothed
(quasi-amicable) pair with partner `n`, then `p` is odd, `a` is odd with `a > 3`, and the
partner `n` is even. -/
