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

namespace Brockian
namespace BetrothedNumbers

/-- Sum-of-divisors function `σ₁`. -/
local notation "σ₁" => ArithmeticFunction.sigma 1

/-- Two positive naturals `n ≠ m` form a *betrothed* (quasi-amicable) pair when the sum of the
divisors of each of them equals `n + m + 1`. -/

theorem partner_unique {k p m : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : σ₁ (2 ^ k * p) = 2 ^ k * p + m + 1) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ, 2 ^ k = T + 1 := ⟨2 ^ k - 1, by have := Nat.one_le_two_pow (n := k); omega⟩
  have hSval : σ₁ (2 ^ k) = 2 * T + 1 := by
    have h1 := sigma_one_two_pow k
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  have h' : (2 * T + 1) * (p + 1) = (T + 1) * p + m + 1 := by
    rw [← hSval, ← sigma_one_two_pow_mul_odd_prime hp hodd, h, hT]
  have hexp : (2 * T + 1) * (p + 1) = 2 * (T * p) + 2 * T + p + 1 := by ring
  have hexp2 : (T + 1) * p = T * p + p := by ring
  have hgoal : m = T * p + 2 * T := by omega
  have hfin : T * (p + 2) = T * p + 2 * T := by ring
  rw [hT]
  simpa using hgoal.trans hfin.symm

/-- Arithmetic contradiction in the case where the two auxiliary primes `2 ^ k - 1` and `p + 2`
are distinct. -/
