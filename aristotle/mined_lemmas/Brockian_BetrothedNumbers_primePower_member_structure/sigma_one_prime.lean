import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction Finset

namespace Brockian
namespace BetrothedNumbers

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair: two distinct
positive integers, each of whose sum of divisors equals `m + n + 1`. -/

theorem sigma_one_prime {p : ℕ} (hp : p.Prime) : sigma 1 p = p + 1 := by
  have := sigma_one_apply_prime_pow (p := p) (i := 1) hp
  simp [Finset.sum_range_succ] at this
  omega

/-- If `n` is odd and `σ n` is odd, then `n` is a perfect square. -/
