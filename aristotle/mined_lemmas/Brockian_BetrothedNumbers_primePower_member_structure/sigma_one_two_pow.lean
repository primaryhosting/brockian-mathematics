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
open scoped ArithmeticFunction.sigma
open ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
two distinct positive integers each of whose sum of divisors equals `m + n + 1`,
equivalently, the sum of the nontrivial proper divisors of each equals the other. -/

lemma sigma_one_two_pow (b : ℕ) : σ 1 (2 ^ b) + 1 = 2 ^ (b + 1) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  induction b with
  | zero => simp
  | succ c ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- Parity of `σ 1 (p ^ b)` for odd `p`: it is congruent to `b + 1` mod `2`. -/
