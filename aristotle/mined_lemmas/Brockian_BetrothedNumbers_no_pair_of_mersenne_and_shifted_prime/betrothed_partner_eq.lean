import Mathlib
/-!
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian.BetrothedNumbers

/-- Two positive natural numbers `m ≠ n` are a *betrothed* (quasi-amicable) pair when the sum of
the divisors of each of them equals `m + n + 1`, i.e. each is the sum of the *proper* divisors
of the other, excluding `1`. -/

theorem betrothed_partner_eq {k p m : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (2 ^ k * p) m) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨-, -, -, hσn, -⟩ := h
  rw [sigma_one_two_pow_mul_odd_prime hp hodd] at hσn
  have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  obtain ⟨q, hq⟩ : ∃ q, 2 ^ k = q + 1 := ⟨2 ^ k - 1, by omega⟩
  have hpow : 2 ^ (k + 1) = 2 * (q + 1) := by rw [pow_succ, hq]; ring
  rw [hpow, hq] at hσn
  have hq1 : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  rw [hq1] at hσn
  have hmq : m = q * (p + 2) := by nlinarith [hσn]
  rw [hmq, hq]
  simp

/-- **Target.** For `k ≥ 2` and an odd prime `p` such that both `2 ^ k - 1` and `p + 2` are prime,
no natural number forms a betrothed pair with `2 ^ k * p`. -/
