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

lemma coprime_sigma_one_primePow {p : ℕ} (hp : p.Prime) (b : ℕ) :
    Nat.Coprime p (σ 1 (p ^ b)) := by
  have h : σ 1 (p ^ b) = p * (∑ k ∈ Finset.range b, p ^ k) + 1 := by
    rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ', Finset.mul_sum]
    ring_nf
  rw [h]
  simp

/-- Multiplicativity of `σ` at `p * t` with `p` prime coprime to `t`. -/
