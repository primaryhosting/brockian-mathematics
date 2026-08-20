/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

/-- `σ₁ n` is the sum of divisors of `n`. -/

lemma four_prod_le_two (a b : ℕ) (hpa : a.Prime) (hab : a < b) :
    4 * (a * b) ≤ 15 * ((a - 1) * (b - 1)) := by
  have ha2 : 2 ≤ a := hpa.two_le
  have hb3 : 3 ≤ b := by omega
  obtain ⟨A, rfl⟩ : ∃ A, a = A + 2 := ⟨a - 2, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B, b = B + 3 := ⟨b - 3, by omega⟩
  have e1 : A + 2 - 1 = A + 1 := by omega
  have e2 : B + 3 - 1 = B + 2 := by omega
  rw [e1, e2]
  nlinarith [Nat.zero_le A, Nat.zero_le B, Nat.zero_le (A * B)]

/-- If a finite set of primes has at most three elements, then
`4 * ∏ p ≤ 15 * ∏ (p - 1)`; i.e. `∏ p/(p-1) ≤ 15/4`. -/
