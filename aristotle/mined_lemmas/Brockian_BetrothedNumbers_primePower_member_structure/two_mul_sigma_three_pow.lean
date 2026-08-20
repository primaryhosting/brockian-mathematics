import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `IsBetrothedPair m n` : `m` and `n` form a betrothed (quasi-amicable) pair, i.e. the sum of
the nontrivial divisors (all divisors except `1` and the number itself) of each equals the other.
Equivalently `σ m = σ n = m + n + 1`.

The classical definition additionally requires `m ≠ n`; that hypothesis is not needed for any of
the results below, so it is omitted here (making the statements slightly stronger). -/

lemma two_mul_sigma_three_pow (t : ℕ) : 2 * σ 1 (3 ^ t) + 1 = 3 ^ (t + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h1 : σ 1 (3 ^ (t + 1)) = σ 1 (3 ^ t) + 3 ^ (t + 1) := by
        rw [sigma_one_apply_prime_pow (by norm_num), sigma_one_apply_prime_pow (by norm_num),
          Finset.sum_range_succ]
      rw [h1]
      have : (3:ℕ) ^ (t + 1 + 1) = 3 * 3 ^ (t + 1) := by ring
      omega

/-- Parity of a geometric sum with odd ratio. -/
