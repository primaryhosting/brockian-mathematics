/-
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- `n` and `m` form a *betrothed* (quasi-amicable) pair: they are distinct positive integers
whose sums of divisors both equal `n + m + 1`. -/

theorem unique_partner {k p m : ℕ} (hk : 2 ≤ k) (hp : p.Prime) (hodd : Odd p)
    (h : IsBetrothedPair (2 ^ k * p) m) : m = (2 ^ k - 1) * (p + 2) := by
  obtain ⟨-, -, -, hn, -⟩ := h
  rw [sigma_one_two_pow_mul_odd_prime hp hodd] at hn
  have hA : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨B, hB⟩ : ∃ B, 2 ^ k = B + 1 := ⟨2 ^ k - 1, by omega⟩
  rw [hB] at hn ⊢
  have hn' : 2 * (B * p) + 2 * B + p + 1 = B * p + p + m + 1 := by
    have : (2 * (B + 1) - 1) * (p + 1) = 2 * (B * p) + 2 * B + p + 1 := by
      have : 2 * (B + 1) - 1 = 2 * B + 1 := by omega
      rw [this]; ring
    rw [this] at hn
    calc 2 * (B * p) + 2 * B + p + 1 = (B + 1) * p + m + 1 := hn
    _ = B * p + p + m + 1 := by ring
  have : m = B * p + 2 * B := by omega
  rw [this]
  simp only [Nat.add_sub_cancel]
  ring

/-- **Target.** Let `k ≥ 2` and let `p` be an odd prime.  If both `2 ^ k - 1` and `p + 2` are
prime, then no number forms a betrothed pair with `2 ^ k * p`. -/
