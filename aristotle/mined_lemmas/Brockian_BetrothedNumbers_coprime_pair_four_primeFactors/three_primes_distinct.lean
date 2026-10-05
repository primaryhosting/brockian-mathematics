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

lemma three_primes_distinct {a b c : ℕ} (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    a * b * c ≤ 4 * ((a - 1) * (b - 1) * (c - 1)) := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · rcases lt_trichotomy b c with h2 | h2 | h2
    · linarith [three_primes_sorted ha hb hc h1 h2]
    · exact absurd h2 hbc
    · rcases lt_trichotomy a c with h3 | h3 | h3
      · linarith [three_primes_sorted ha hc hb h3 h2]
      · exact absurd h3 hac
      · linarith [three_primes_sorted hc ha hb h3 h1]
  · exact absurd h1 hab
  · rcases lt_trichotomy a c with h2 | h2 | h2
    · linarith [three_primes_sorted hb ha hc h1 h2]
    · exact absurd h2 hac
    · rcases lt_trichotomy b c with h3 | h3 | h3
      · linarith [three_primes_sorted hb hc ha h3 h2]
      · exact absurd h3 hbc
      · linarith [three_primes_sorted hc hb ha h3 h1]

/-- For a set of at most three primes, `∏ p ≤ 4 * ∏ (p - 1)`. -/
