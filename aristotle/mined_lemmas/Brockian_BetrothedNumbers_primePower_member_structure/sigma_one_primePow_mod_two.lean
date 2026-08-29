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

lemma sigma_one_primePow_mod_two {p : ℕ} (hp : p.Prime) (hodd : Odd p) (b : ℕ) :
    σ 1 (p ^ b) % 2 = (b + 1) % 2 := by
  rw [sigma_one_apply_prime_pow hp]
  induction b with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ]
    have hpow : p ^ (c + 1) % 2 = 1 := Nat.odd_iff.mp (hodd.pow)
    omega

/-! ### Upper and lower bounds for `σ` -/

/-- Crude Gauss bound: `2 * σ 1 k ≤ k * (k + 1)`. -/
