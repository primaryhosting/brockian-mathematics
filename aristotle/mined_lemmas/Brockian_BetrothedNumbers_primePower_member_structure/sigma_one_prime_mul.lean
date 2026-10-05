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

lemma sigma_one_prime_mul {p t : ℕ} (hp : p.Prime) (h : Nat.Coprime p t) :
    σ 1 (p * t) = (p + 1) * σ 1 t := by
  rw [isMultiplicative_sigma.map_mul_of_coprime h, sigma_one_prime hp]

/-- `σ 1 (2 ^ b) = 2 ^ (b + 1) - 1`, in additive form. -/
