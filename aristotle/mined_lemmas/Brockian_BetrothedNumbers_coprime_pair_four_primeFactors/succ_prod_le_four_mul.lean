import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction Finset

/-- `Betrothed m n` says that `m` and `n` are *betrothed* (quasi-amicable) numbers:
both are positive and each one's sum of divisors equals `m + n + 1`. -/

lemma succ_prod_le_four_mul (A B C : ℕ) (hA : 1 ≤ A) (hB : 2 ≤ B) (hC : 4 ≤ C) :
    (A + 1) * (B + 1) * (C + 1) ≤ 4 * (A * B * C) := by
  obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, B = b + 2 := ⟨B - 2, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 4 := ⟨C - 4, by omega⟩
  nlinarith [Nat.zero_le (a * b * c), Nat.zero_le (a * b), Nat.zero_le (a * c),
    Nat.zero_le (b * c)]

/-- Three increasing primes: `a * b * c ≤ 4 * ((a-1) * (b-1) * (c-1))`. -/
