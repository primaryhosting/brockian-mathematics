/-
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 1000000

namespace Brockian
namespace BetrothedNumbers

/-- `Betrothed m n` says that `m` and `n` form a pair of betrothed (quasi-amicable)
numbers: they are distinct positive integers each of whose sum of divisors equals
`m + n + 1` (equivalently, the sum of the *proper* divisors of each, excluding `1`
and the number itself, is the other number). -/

lemma three_core (x y z : ℕ) (hx : 1 ≤ x) (hy : 2 ≤ y) (hz : 4 ≤ z) :
    (x + 1) * (y + 1) * (z + 1) ≤ 4 * (x * y * z) := by
  obtain ⟨a, rfl⟩ : ∃ a, x = 1 + a := ⟨x - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = 2 + b := ⟨y - 2, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, z = 4 + c := ⟨z - 4, by omega⟩
  nlinarith [Nat.zero_le a, Nat.zero_le b, Nat.zero_le c, Nat.zero_le (a * b),
    Nat.zero_le (a * c), Nat.zero_le (b * c), Nat.zero_le (a * b * c)]

/-- For three distinct positive integers none of which equals `3` (this holds for
`p - 1` with `p` prime, since `4` is not prime), the product bound holds. -/
