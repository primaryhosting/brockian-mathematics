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

lemma sigma_one_primePow_add_two {p : ℕ} (hp : p.Prime) (b : ℕ) :
    σ 1 (p ^ (b + 2)) = p ^ (b + 2) + p * σ 1 (p ^ b) + 1 := by
  rw [sigma_one_apply_prime_pow hp, sigma_one_apply_prime_pow hp, Finset.sum_range_succ',
    Finset.sum_range_succ, Finset.mul_sum]
  ring_nf

/-- A prime `p` is coprime to `σ 1 (p ^ b)`. -/
