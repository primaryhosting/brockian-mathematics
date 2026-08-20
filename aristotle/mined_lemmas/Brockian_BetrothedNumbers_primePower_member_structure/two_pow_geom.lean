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

lemma two_pow_geom (c : ℕ) : (∑ i ∈ Finset.range c, (2:ℕ) ^ i) + 1 = 2 ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [Finset.sum_range_succ]
      have : (2:ℕ) ^ (c + 1) = 2 * 2 ^ c := by ring
      omega

/-! ### Structure of the partner of a prime power -/

/-- If `p ^ a` belongs to a betrothed pair with partner `n`, then `a = c + 1` with `c ≥ 1`
and `n = p * (1 + p + ⋯ + p ^ (c-1))`. -/
