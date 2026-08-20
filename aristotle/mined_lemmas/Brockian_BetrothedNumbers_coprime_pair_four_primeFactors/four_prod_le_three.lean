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

lemma four_prod_le_three (a b c : ℕ) (hpa : a.Prime) (hpc : c.Prime)
    (hab : a < b) (hbc : b < c) :
    4 * (a * b * c) ≤ 15 * ((a - 1) * ((b - 1) * (c - 1))) := by
  have ha2 : 2 ≤ a := hpa.two_le
  have hb3 : 3 ≤ b := by omega
  have hc5 : 5 ≤ c := by
    have h4 : c ≠ 4 := by
      rintro rfl
      norm_num at hpc
    omega
  obtain ⟨A, rfl⟩ : ∃ A, a = A + 2 := ⟨a - 2, by omega⟩
  obtain ⟨B, rfl⟩ : ∃ B, b = B + 3 := ⟨b - 3, by omega⟩
  obtain ⟨C, rfl⟩ : ∃ C, c = C + 5 := ⟨c - 5, by omega⟩
  have e1 : A + 2 - 1 = A + 1 := by omega
  have e2 : B + 3 - 1 = B + 2 := by omega
  have e3 : C + 5 - 1 = C + 4 := by omega
  rw [e1, e2, e3]
  nlinarith [Nat.zero_le A, Nat.zero_le B, Nat.zero_le C, Nat.zero_le (A * B),
    Nat.zero_le (A * C), Nat.zero_le (B * C), Nat.zero_le (A * B * C)]

/-- Two increasing primes: `4 * a * b ≤ 15 * (a-1) * (b-1)`. -/
